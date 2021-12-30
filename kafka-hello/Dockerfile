
FROM ubuntu:latest
LABEL author="frozenlight"
WORKDIR /root

EXPOSE 22
RUN apt update && apt -y install ssh
COPY id_rsa.pub /root/.ssh/authorized_keys
COPY start-ssh.sh /root/start-ssh.sh

CMD [ "/bin/bash", "/root/start-ssh.sh" ]
