package main

import (
	"log"
	"strconv"
	"sync/atomic"
	"time"

	"github.com/Shopify/sarama"
)

const (
	WAFHost  = "10.129.101.65:9093"
	Host1    = "172.18.0.3:9092"
	Host2    = "172.18.0.6:9092"
	Topic    = "jytest"
	WAFTopic = "toc-appinfra-waf-test-sg"
)

func SyncProducer(limit int) {
	config := sarama.NewConfig()
	// 同步生产者必须同时开启 Return.Successes 和 Return.Errors
	// 因为同步生产者在发送之后就必须返回状态，所以需要两个都返回
	config.Producer.Return.Successes = true
	config.Producer.Return.Errors = true // 这个默认值就是 true 可以不用手动 赋值
	// async/sync 生产者逻辑是一致的，Success/Errors都是通过channel返回
	// 只是 sync 封装了一层，等 channel 返回之后才返回给调用者

	producer, err := sarama.NewSyncProducer([]string{Host1, Host2}, config)
	if err != nil {
		log.Fatal("NewSyncProducer err:", err)
	}
	defer producer.Close()

	for i := 0; i < limit; i++ {
		str := strconv.Itoa(int(time.Now().Unix()))
		msg := &sarama.ProducerMessage{Topic: Topic, Key: sarama.StringEncoder(strconv.Itoa(i)), Value: sarama.StringEncoder(str)}
		partition, offset, err := producer.SendMessage(msg) // 发送逻辑也是封装的异步发送逻辑(将异步封装成了同步)
		if err != nil {
			log.Println("SendMessage err: ", err)
			continue
		}
		time.Sleep(1 * time.Second)
		log.Printf("[Producer] partitionid: %d; offset:%d, value: %s\n", partition, offset, str)
	}
}

func AsyncProducer(topic string, limit int) {
	count := int32(0)
	config := sarama.NewConfig()
	// 异步生产者不建议把 Errors 和 Successes 都开启，一般开启 Errors 就行
	// 同步生产者就必须都开启，因为会同步返回发送成功或者失败
	config.Producer.Return.Errors = false   // 设定需要返回错误信息
	config.Producer.Return.Successes = true // 设定需要返回成功信息
	producer, err := sarama.NewAsyncProducer([]string{Host1, Host2}, config)
	if err != nil {
		log.Fatal("NewSyncProducer err:", err)
	}
	defer producer.AsyncClose()
	go func() {
		// [!important] 异步生产者发送后必须把返回值从 Errors 或者 Successes 中读出来 不然会阻塞 sarama 内部处理逻辑 导致只能发出去一条消息
		for {
			select {
			case s := <-producer.Successes():
				log.Printf("[Producer] key:%v msg:%+v \n", s.Key, s.Value)
			case e := <-producer.Errors():
				if e != nil {
					log.Printf("[Producer] err:%v msg:%+v \n", e.Msg, e.Err)
				}
			}
		}
	}()

	// 异步发送
	for i := 0; i < limit; i++ {
		str := strconv.Itoa(int(time.Now().UnixNano()))
		msg := &sarama.ProducerMessage{Topic: topic, Key: nil, Value: sarama.StringEncoder(str)}
		// 异步发送只是写入内存了就返回了，并没有真正发送出去
		// sarama 库中用的是一个 channel 来接收，后台 goroutine 异步从该 channel 中取出消息并真正发送
		producer.Input() <- msg
		atomic.AddInt32(&count, 1)
		if atomic.LoadInt32(&count)%1000 == 0 {
			log.Printf("已发送消息数:%v\n", count)
		}

	}
	log.Printf("发送完毕 总发送消息数:%v\n", limit)
}

func main() {
	SyncProducer(4)
}
