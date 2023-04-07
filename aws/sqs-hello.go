package main

import (
	"fmt"

	"github.com/aws/aws-sdk-go/aws"
	"github.com/aws/aws-sdk-go/aws/session"
	"github.com/aws/aws-sdk-go/service/iam"
	"github.com/aws/aws-sdk-go/service/sqs"
)

func GetQueueURL(sqsClient *sqs.SQS, queueName string) string {
	result, err := sqsClient.GetQueueUrl(&sqs.GetQueueUrlInput{
		QueueName: &queueName,
	})
	if err != nil {
		fmt.Printf("Got an error while trying to get URL: %v", err)
		return ""
	}
	fmt.Println("Got Queue URL: " + *result.QueueUrl)
	return *result.QueueUrl
}

func GetMe(sess *session.Session) {
	svc := iam.New(sess)
	result, err := svc.ListUsers(&iam.ListUsersInput{
		MaxItems: aws.Int64(10),
	})
	if err != nil {
		fmt.Println("Error", err)
		return
	}
	fmt.Printf("Users: %+v\n", result)
}

func SendMessage(sess *session.Session, queueName string) {
	sqsClient := sqs.New(sess)

	queueUrl := GetQueueURL(sqsClient, queueName)
	messageBody := "This is a test message"

	sendResult, err := sqsClient.SendMessage(&sqs.SendMessageInput{
		QueueUrl:    &queueUrl,
		MessageBody: aws.String(messageBody),
	})
	if err != nil {
		fmt.Printf("Got an error while trying to send message to queue: %v", err)
		return
	}
	fmt.Println(*sendResult.MessageId)
	return
}

func GetMessages(sess *session.Session, queueName string, maxMessages int) {
	sqsClient := sqs.New(sess)
	queueUrl := GetQueueURL(sqsClient, queueName)

	msgResult, err := sqsClient.ReceiveMessage(&sqs.ReceiveMessageInput{
		QueueUrl:            &queueUrl,
		MaxNumberOfMessages: aws.Int64(int64(maxMessages)),
	})
	if err != nil {
		fmt.Println(err)
		return
	}

	for _, m := range msgResult.Messages {
		fmt.Println(m.GoString())
	}

	return
}

func main() {
	sess, err := session.NewSessionWithOptions(session.Options{
		Profile: "default",
		Config: aws.Config{
			Region: aws.String("ap-southeast-1"),
		},
	})
	if err != nil {
		fmt.Printf("Failed to initialize new session: %v", err)
		return
	}

	// SendMessage(sess, "jysqs")
	GetMessages(sess, "jysqs", 10)
}
