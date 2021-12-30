
-- Create user on master server
show master status;
CREATE USER 'slave'@'%' IDENTIFIED BY '123456';
GRANT REPLICATION SLAVE, REPLICATION CLIENT ON *.* TO 'slave'@'%';

-- Start slave
-- Need to copy pubkey from master first!
CHANGE MASTER TO MASTER_HOST='172.17.0.2', MASTER_USER='slave', MASTER_PASSWORD='123456', MASTER_LOG_FILE='mysql-bin.000004',master_log_pos=3761,master_port=3306;
start slave;
show slave status \G