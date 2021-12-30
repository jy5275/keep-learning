#!/bin/bash
# Download go1.16
wget https://dl.google.com/go/go1.16.4.linux-amd64.tar.gz

# Launch zk and Kafka containers
docker run --name zookeeper --network app-tier -e ALLOW_ANONYMOUS_LOGIN=yes -p 2181:2181 bitnami/zookeeper:latest
docker run --name kafka1 --network app-tier -e KAFKA_CFG_ZOOKEEPER_CONNECT=zookeeper:2181 -e ALLOW_PLAINTEXT_LISTENER=yes -p :9092 bitnami/kafka:latest
docker run --name kafka2 --network app-tier -e KAFKA_CFG_ZOOKEEPER_CONNECT=zookeeper:2181 -e ALLOW_PLAINTEXT_LISTENER=yes -p :9092 bitnami/kafka:latest

# Web UI: https://github.com/obsidiandynamics/kafdrop
docker run -d --rm -p 9000:9000 \
    --network app-tier \
    -e KAFKA_BROKERCONNECT=<host:port,host:port> \
    -e JVM_OPTS="-Xms32M -Xmx64M" \
    -e SERVER_SERVLET_CONTEXTPATH="/" \
    obsidiandynamics/kafdrop

# Another container as console
docker build -f Dockerfile -t frozenlight/ubuntu-ssh .
docker run -d --network app-tier -p 2222:22 --name console frozenlight/ubuntu-ssh

# Launch a producer
ansible-playbook plays.yml

