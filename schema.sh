sqlite3 mailbox.db <<EOF

drop table mail;
create table mail (
    id integer primary key autoincrement,
    from_addr varchar(50),
    date datetime default(datetime('now'))
);

drop table tag;
create table tag (
    id integer primary key autoincrement,
    name varchar(50) unique
);

drop table tagmail;
create table tagmail (
    id integer primary key autoincrement,
    tag_id int references tag(id),
    mail_id int references mail(id)
);

drop view mailbox;
create view mailbox as
select mail.id as mail_id,
       mail.from_addr as from_addr,
       mail.date as date,
       tag.id as tag_id,
       tag.name as tag_name
from 
       mail,tagmail,tag 
where 
       mail.id = tagmail.mail_id and 
       tag.id = tagmail.tag_id;

insert into mail(from_addr) values('alice@example.com');
insert into mail(from_addr) values('alice@example.com');
insert into mail(from_addr) values('bob@example.org');
insert into mail(from_addr) values('bob@example.org');
insert into mail(from_addr) values('bob@example.org');

insert into tag(name) values('alice');
insert into tag(name) values('bob');

insert into tagmail(tag_id,mail_id)
  select 
    tag_id,mail_id 
  from 
    (select id as mail_id from mail where from_addr like 'alice%'), 
    (select id as tag_id from tag where name = 'alice');
insert into tagmail(tag_id,mail_id)
  select 
    tag_id,mail_id 
  from 
    (select id as mail_id from mail where from_addr like 'bob%'), 
    (select id as tag_id from tag where name = 'bob');

EOF
