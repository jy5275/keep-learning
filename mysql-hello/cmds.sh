# Full tutorial: https://www.cnblogs.com/songwenjie/p/9371422.html
docker exec -it mysql2 bash

# Start
docker run --name mysql1 -v /Users/yan.jiang/repos/mysql-hello/mysql:/etc/mysql -d -e MYSQL_ROOT_PASSWORD=root mysql
docker run --name mysql2 -v /Users/yan.jiang/repos/mysql-hello/mysql2:/etc/mysql -d -e MYSQL_ROOT_PASSWORD=root mysql

# Test external access
docker run -it --network 5ab637db7834f8d4e8d27c423d6ffe829df95878cb02b232ff4a233e108df227 mysql mysql -h 172.17.0.2 -u root -p

mysqldump -uroot -p'123456' --all-databases > mysql_bak.$(date +%F).sql
# https://www.bbsmax.com/A/gAJGpDYX5Z/
mysql --ssl-mode=DISABLED -h 172.17.0.2 -uslave -p123456 --get-server-public-key
