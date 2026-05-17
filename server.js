// ═══════════════════════════════════════════════════════
// server.js — Survival Multiplayer Server
// node server.js → http://localhost:3000
// ═══════════════════════════════════════════════════════
var express=require('express'),http=require('http'),{Server}=require('socket.io'),path=require('path');
var app=express(),server=http.createServer(app),io=new Server(server);
app.use('/lib',express.static(path.join(__dirname,'lib')));
app.use(express.static(path.join(__dirname,'public')));
app.get('/',function(req,res){res.sendFile(path.join(__dirname,'public','index.html'));});

// ═══ PERLIN ═══
class Pn{constructor(s){var p=new Uint8Array(256);for(var i=0;i<256;i++)p[i]=i;for(var i=255;i>0;i--){s=(s*16807+12345)&0x7fffffff;var j=s%(i+1);var tmp=p[i];p[i]=p[j];p[j]=tmp;}this.p=new Uint8Array(512);this.m=new Uint8Array(512);for(var i=0;i<512;i++){this.p[i]=p[i&255];this.m[i]=this.p[i]%12;}}n(x,y){var G=[1,1,0,-1,1,0,1,-1,0,-1,-1,0,1,0,1,-1,0,1,1,0,-1,-1,0,-1,0,1,1,0,-1,1,0,1,-1,0,-1,-1];var X=Math.floor(x)&255,Y=Math.floor(y)&255,xf=x-Math.floor(x),yf=y-Math.floor(y);var u=xf*xf*xf*(xf*(xf*6-15)+10),v=yf*yf*yf*(yf*(yf*6-15)+10);var p=this.p,m=this.m,a=m[X+p[Y]]*3,b=m[X+1+p[Y]]*3,c=m[X+p[Y+1]]*3,d=m[X+1+p[Y+1]]*3;return(G[a]*xf+G[a+1]*yf)+u*((G[b]*(xf-1)+G[b+1]*yf)-(G[a]*xf+G[a+1]*yf))+v*((G[c]*xf+G[c+1]*(yf-1))+u*((G[d]*(xf-1)+G[d+1]*(yf-1))-(G[c]*xf+G[c+1]*(yf-1)))-((G[a]*xf+G[a+1]*yf)+u*((G[b]*(xf-1)+G[b+1]*yf)-(G[a]*xf+G[a+1]*yf))));}}
var pn=new Pn(42);
function fbm(x,z,o){var v=0,a=1,f=1,mx=0;o=o||6;for(var i=0;i<o;i++){v+=a*pn.n(x*f,z*f);mx+=a;a*=.48;f*=2.03;}return v/mx;}
function gH(x,z){return fbm(x*.005,z*.005,6)*22+fbm(x*.018+50,z*.018+50,4)*5+fbm(x*.07+100,z*.07+100,2)*1.2;}

// ═══ CONFIG ═══
var W=500,BND=242,WY=-3,CYCLE=480,MAX_PLAYERS=8,MAX_ENEMIES=10,SPAWN_INTERVAL=12;
var ENEMY_TYPES={
  slime:{name:'Slime',hp:30,dmg:5,spd:2.5,detect:8,atkRange:1.5,atkCD:2,nightOnly:false,maxCount:4,loot:{bush:2}},
  wolf:{name:'Wolf',hp:55,dmg:12,spd:5,detect:15,atkRange:2,atkCD:1.5,nightOnly:false,maxCount:3,loot:{bush:3}},
  night:{name:'Shadow',hp:90,dmg:25,spd:7,detect:25,atkRange:2.2,atkCD:1,nightOnly:true,maxCount:3,loot:{bush:5}}
};
var RES_CFG={tree:{name:'Wood',resp:60,max:90},stone:{name:'Stone',resp:120,max:60},bush:{name:'Food',resp:45,max:45}};
var STRUCT_CFG={
  wall:{name:'Wall',w:2,h:2.2,d:0.3,cost:{tree:5},maxHP:100},
  door:{name:'Door',w:2,h:2.2,d:0.3,cost:{tree:3,stone:1},maxHP:80},
  floor:{name:'Floor',w:2,h:0.1,d:2,cost:{tree:2},maxHP:60,noBlock:true},
  campfire_s:{name:'Campfire',w:1,h:0.5,d:1,cost:{tree:5,stone:2},maxHP:50,noBlock:true},
  storage:{name:'Storage',w:1.2,h:1,d:1.2,cost:{tree:4},maxHP:80}
};

// ═══ ROOMS ═══
var rooms=new Map();
function generateCode(){var c='ABCDEFGHJKLMNPQRSTUVWXYZ23456789',code;do{code='';for(var i=0;i<6;i++)code+=c[Math.floor(Math.random()*c.length)];}while(rooms.has(code));return code;}

function generateResources(){
  var r=new Map(),wS=999,rId=0;
  function wR(){wS=(wS*16807+12345)&0x7fffffff;return wS/0x7fffffff;}
  for(var t in RES_CFG){var cfg=RES_CFG[t],pl=0,at=0;
    while(pl<cfg.max&&at<cfg.max*15){at++;var rx=(wR()-.5)*(W-24),rz=(wR()-.5)*(W-24),rh=gH(rx,rz);
      if(rh<WY+.5||rh>18)continue;r.set(rId,{id:rId,type:t,x:rx,z:rz,alive:true,respawnTimer:0,maxResp:cfg.resp});rId++;pl++;}}
  return r;
}

function pNet(p){return{id:p.id,name:p.name,x:p.x,y:p.y,z:p.z,rotY:p.rotY,health:p.health,hunger:p.hunger,equipped:p.equipped,isDead:p.isDead};}
function eNet(e){return{id:e.id,typeKey:e.typeKey,x:e.x,y:e.y,z:e.z,hp:e.hp,maxHp:e.maxHp,state:e.state,hitFlash:e.hitFlash||0,rotY:e.rotY||0};}
function sNet(s){return{id:s.id,type:s.type,x:s.x,z:s.z,rotation:s.rotation,hp:s.hp,ownerId:s.ownerId,storage:s.storage};}
function getPlayerRoom(sid){var f=null;rooms.forEach(function(r){if(r.players.has(sid))f=r;});return f;}
function broadcastRoomList(code){var room=rooms.get(code);if(!room)return;var list=[];room.players.forEach(function(p){list.push({id:p.id,name:p.name});});io.to(code).emit('player_list',list);}

function createRoom(cid,cname){
  var code=generateCode();
  var room={code:code,players:new Map(),enemies:new Map(),resources:generateResources(),structures:new Map(),structIdCtr:0,gameTime:0,enemyIdCtr:0,spawnTimer:8,sunHeight:1,loop:null};
  room.loop=setInterval(function(){updateRoom(room);},50);
  rooms.set(code,room);console.log('[ROOM] '+code+' by '+cname);return room;
}
function joinRoom(room,sid,name){
  var sx=(Math.random()-.5)*20,sz=(Math.random()-.5)*20,sy=gH(sx,sz);
  var p={id:sid,name:name,x:sx,y:sy,z:sz,rotY:0,health:100,hunger:100,equipped:null,isDead:false,lastAtk:0};
  room.players.set(sid,p);return p;
}
function leaveRoom(sid){
  rooms.forEach(function(room,code){
    if(room.players.has(sid)){var p=room.players.get(sid);room.players.delete(sid);
      io.to(code).emit('player_left',{id:sid});broadcastRoomList(code);
      if(room.players.size===0){clearInterval(room.loop);rooms.delete(code);console.log('[ROOM] '+code+' deleted');}}
  });
}

// ═══ COLLISION ═══
function wallCollision(room,nx,nz,radius){
  var blocked=false;var r=radius||0.3;
  room.structures.forEach(function(s){
    if(blocked)return;var cfg=STRUCT_CFG[s.type];if(!cfg||cfg.noBlock)return;
    var hw=cfg.w/2+r,hd=cfg.d/2+r;
    var rot=s.rotation||0;
    if(rot===Math.PI/2||rot===Math.PI*1.5){var t=hw;hw=hd;hd=t;}
    if(nx>s.x-hw&&nx<s.x+hw&&nz>s.z-hd&&nz<s.z+hd)blocked=true;
  });
  return blocked;
}

// ═══ ROOM UPDATE ═══
function updateRoom(room){
  var dt=.05;room.gameTime+=dt;
  room.sunHeight=Math.sin((room.gameTime%CYCLE)/CYCLE*Math.PI*2-Math.PI/2);

  room.enemies.forEach(function(e,id){
    if(e.hp<=0)return;
    var nearD=Infinity,nearP=null;
    room.players.forEach(function(p){if(p.isDead)return;var d=Math.sqrt((p.x-e.x)**2+(p.z-e.z)**2);if(d<nearD){nearD=d;nearP=p;}});
    if(nearD<e.type.detect)e.state=(nearD<e.type.atkRange)?'attack':'chase';
    else if(e.state==='chase'){e.state='idle';e.stateTimer=2+Math.random()*2;}
    e.stateTimer-=dt;e.atkCD=Math.max(0,e.atkCD-dt);

    if(e.state==='idle'){
      if(e.stateTimer<=0){e.state='patrol';
        e.patrolX=Math.max(-BND,Math.min(BND,e.x+(Math.random()-.5)*15));
        e.patrolZ=Math.max(-BND,Math.min(BND,e.z+(Math.random()-.5)*15));
        e.stateTimer=4+Math.random()*3;}
    }else if(e.state==='patrol'){
      var pdx=e.patrolX-e.x,pdz=e.patrolZ-e.z,pd=Math.sqrt(pdx*pdx+pdz*pdz);
      if(pd>.5){var step=e.type.spd*.5*dt,nx=e.x+(pdx/pd)*step,nz=e.z+(pdz/pd)*step;
        if(!wallCollision(room,nx,nz)){e.x=nx;e.z=nz;}e.rotY=Math.atan2(pdx,pdz);}
      else{e.state='idle';e.stateTimer=2+Math.random()*2;}
      if(e.stateTimer<=0){e.state='idle';e.stateTimer=1;}
    }else if(e.state==='chase'&&nearP){
      var dx=nearP.x-e.x,dz=nearP.z-e.z,d=Math.sqrt(dx*dx+dz*dz);
      if(d>.5){var step=e.type.spd*dt,nx=e.x+(dx/d)*step,nz=e.z+(dz/d)*step;
        if(!wallCollision(room,nx,nz)){e.x=nx;e.z=nz;}
        else{var nx2=e.x+(dx/d)*step;if(!wallCollision(room,nx2,e.z))e.x=nx2;
          var nz2=e.z+(dz/d)*step;if(!wallCollision(room,e.x,nz2))e.z=nz2;}
        e.rotY=Math.atan2(dx,dz);}
    }else if(e.state==='attack'&&nearP){
      e.rotY=Math.atan2(nearP.x-e.x,nearP.z-e.z);
      if(nearD>e.type.atkRange*1.5)e.state='chase';
      else if(e.atkCD<=0&&!nearP.isDead){
        e.atkCD=e.type.atkCD;var dmg=e.type.dmg;
        io.to(room.code).emit('player_hurt',{id:nearP.id,dmg:dmg});
        var d2=Math.sqrt((nearP.x-e.x)**2+(nearP.z-e.z)**2)||1;
        nearP.x+=((nearP.x-e.x)/d2)*1.2;nearP.z+=((nearP.z-e.z)/d2)*1.2;}
    }
    if(Math.abs(e.kbX)>.05||Math.abs(e.kbZ)>.05){
      var bkx=e.x+e.kbX*dt*3,bkz=e.z+e.kbZ*dt*3;
      if(!wallCollision(room,bkx,bkz)){e.x=bkx;e.z=bkz;}
      e.kbX*=.85;e.kbZ*=.85;
      e.x=Math.max(-BND,Math.min(BND,e.x));e.z=Math.max(-BND,Math.min(BND,e.z));}
    e.y=gH(e.x,e.z);e.hitFlash=Math.max(0,(e.hitFlash||0)-dt);
    if(e.type.nightOnly&&room.sunHeight>.15)room.enemies.delete(id);
    if(nearD>120)room.enemies.delete(id);
  });

  room.spawnTimer-=dt;
  if(room.spawnTimer<=0&&room.players.size>0){room.spawnTimer=SPAWN_INTERVAL+Math.random()*5;spawnEnemy(room);}

  room.resources.forEach(function(r){
    if(!r.alive){r.respawnTimer-=dt;if(r.respawnTimer<=0){r.alive=true;io.to(room.code).emit('resource_respawned',{id:r.id});}}
  });

  if(room.players.size>0){
    var enArr=[];room.enemies.forEach(function(e){enArr.push(eNet(e));});
    io.to(room.code).emit('enemies',enArr);
    var plArr=[];room.players.forEach(function(p){plArr.push(pNet(p));});
    io.to(room.code).emit('players',plArr);
  }
}

function spawnEnemy(room){
  var alive=0;room.enemies.forEach(function(e){if(e.hp>0)alive++;});
  if(alive>=MAX_ENEMIES||room.players.size===0)return;
  var isNight=room.sunHeight<-.1,roll=Math.random(),typeKey;
  if(isNight&&roll<.25)typeKey='night';else if(roll<.55)typeKey='slime';else typeKey='wolf';
  var type=ENEMY_TYPES[typeKey],tc=0;
  room.enemies.forEach(function(e){if(e.typeKey===typeKey&&e.hp>0)tc++;});
  if(tc>=type.maxCount)return;
  var pArr=Array.from(room.players.values()),target=pArr[Math.floor(Math.random()*pArr.length)];
  var angle=Math.random()*Math.PI*2,dist=40+Math.random()*20;
  var ex=Math.max(-BND+5,Math.min(BND-5,target.x+Math.cos(angle)*dist));
  var ez=Math.max(-BND+5,Math.min(BND-5,target.z+Math.sin(angle)*dist));
  var ey=gH(ex,ez);if(ey<WY+1)return;
  var id=room.enemyIdCtr++;
  room.enemies.set(id,{id:id,typeKey:typeKey,type:type,x:ex,y:ey,z:ez,hp:type.hp,maxHp:type.hp,state:'idle',stateTimer:2+Math.random()*3,atkCD:0,hitFlash:0,kbX:0,kbZ:0,rotY:0,patrolX:ex+(Math.random()-.5)*10,patrolZ:ez+(Math.random()-.5)*10});
}

// ═══ SOCKET ═══
io.on('connection',function(socket){
  console.log('[CONN] '+socket.id);

  socket.on('create_room',function(data){
    var name=(data.name||'Player').substring(0,16).trim()||'Player';
    leaveRoom(socket.id);var room=createRoom(socket.id,name);
    var player=joinRoom(room,socket.id,name);socket.join(room.code);
    socket.emit('room_created',{code:room.code});enterGame(socket,room,player);
  });

  socket.on('join_room',function(data){
    var name=(data.name||'Player').substring(0,16).trim()||'Player';
    var code=(data.code||'').toUpperCase().trim();
    if(!rooms.has(code)){socket.emit('room_error',{msg:'Room not found!'});return;}
    var room=rooms.get(code);
    if(room.players.size>=MAX_PLAYERS){socket.emit('room_error',{msg:'Room full! (max 8)'});return;}
    leaveRoom(socket.id);var player=joinRoom(room,socket.id,name);socket.join(code);
    enterGame(socket,room,player);
  });

  function enterGame(sock,room,player){
    var resObj={};room.resources.forEach(function(r,id){resObj[id]={alive:r.alive};});
    var enArr=[];room.enemies.forEach(function(e){enArr.push(eNet(e));});
    var stArr=[];room.structures.forEach(function(s){stArr.push(sNet(s));});
    sock.emit('joined',{playerId:player.id,players:Array.from(room.players.values()).map(pNet),resources:resObj,structures:stArr,enemies:enArr,gameTime:room.gameTime,code:room.code});
    sock.to(room.code).emit('player_joined',pNet(player));broadcastRoomList(room.code);
  }

  socket.on('pos',function(data){var room=getPlayerRoom(socket.id);if(!room)return;var p=room.players.get(socket.id);if(!p)return;p.x=data.x;p.y=data.y;p.z=data.z;p.rotY=data.rotY;if(data.equipped!==undefined)p.equipped=data.equipped;});

  socket.on('update_state',function(data){var room=getPlayerRoom(socket.id);if(!room)return;var p=room.players.get(socket.id);if(!p)return;if(data.health!==undefined)p.health=data.health;if(data.hunger!==undefined)p.hunger=data.hunger;if(data.isDead!==undefined)p.isDead=data.isDead;});

  // ✅ CORREÇÃO: forward vector com Math.sin (sem negativo)
  socket.on('attack',function(data){
    var room=getPlayerRoom(socket.id);if(!room)return;var p=room.players.get(socket.id);if(!p||p.isDead)return;
    var now=Date.now();if(now-p.lastAtk<350)return;p.lastAtk=now;
    var dmg=data.dmg||8,range=3.2,fwd={x:Math.sin(p.rotY),z:-Math.cos(p.rotY)},bestE=null,bestD=range;
    room.enemies.forEach(function(e){if(e.hp<=0)return;var dx=e.x-p.x,dz=e.z-p.z,dist=Math.sqrt(dx*dx+dz*dz);if(dist>range)return;var dot=fwd.x*(dx/dist)+fwd.z*(dz/dist),angle=Math.acos(Math.max(-1,Math.min(1,dot)));if(angle<Math.PI/3&&dist<bestD){bestD=dist;bestE=e;}});
    if(bestE){bestE.hp-=dmg;bestE.hitFlash=.3;bestE.state='chase';
      var d=Math.sqrt((bestE.x-p.x)**2+(bestE.z-p.z)**2)||1;
      bestE.kbX=((bestE.x-p.x)/d)*4;bestE.kbZ=((bestE.z-p.z)/d)*4;
      io.to(room.code).emit('enemy_hit',{id:bestE.id,hp:bestE.hp,dmg:dmg});
      if(bestE.hp<=0){var loot=ENEMY_TYPES[bestE.typeKey].loot;io.to(room.code).emit('enemy_killed',{id:bestE.id,killerId:socket.id,loot:loot});room.enemies.delete(bestE.id);}}
  });

  socket.on('collect',function(data){var room=getPlayerRoom(socket.id);if(!room)return;var r=room.resources.get(data.id);if(!r||!r.alive)return;r.alive=false;r.respawnTimer=r.maxResp;io.to(room.code).emit('resource_collected',{id:data.id,by:socket.id,type:r.type});});

  socket.on('place_structure',function(data){
    var room=getPlayerRoom(socket.id);if(!room)return;var p=room.players.get(socket.id);if(!p||p.isDead)return;
    var type=data.type,cfg=STRUCT_CFG[type];if(!cfg)return;
    var gx=Math.round((data.x||0)/2)*2,gz=Math.round((data.z||0)/2)*2,rot=data.rotation||0;
    var dist=Math.sqrt((p.x-gx)**2+(p.z-gz)**2);if(dist>10)return;
    var occupied=false;room.structures.forEach(function(s){if(Math.abs(s.x-gx)<1.8&&Math.abs(s.z-gz)<1.8)occupied=true;});
    if(occupied)return;
    var id=room.structIdCtr++;
    var structure={id:id,type:type,x:gx,z:gz,y:gH(gx,gz),rotation:rot,hp:cfg.maxHP,ownerId:socket.id,storage:type==='storage'?[]:null};
    room.structures.set(id,structure);io.to(room.code).emit('structure_placed',sNet(structure));
  });

  socket.on('destroy_structure',function(data){var room=getPlayerRoom(socket.id);if(!room)return;var s=room.structures.get(data.id);if(!s)return;room.structures.delete(s.id);io.to(room.code).emit('structure_destroyed',{id:s.id});});

  socket.on('storage_deposit',function(data){var room=getPlayerRoom(socket.id);if(!room)return;var s=room.structures.get(data.id);if(!s||s.type!=='storage'||!s.storage)return;s.storage.push({type:data.item,qty:data.qty||1});io.to(room.code).emit('storage_update',{id:s.id,storage:s.storage});});

  socket.on('storage_withdraw',function(data){var room=getPlayerRoom(socket.id);if(!room)return;var s=room.structures.get(data.id);if(!s||s.type!=='storage'||!s.storage)return;var idx=data.index;if(idx<0||idx>=s.storage.length)return;s.storage.splice(idx,1);io.to(room.code).emit('storage_update',{id:s.id,storage:s.storage});});

  socket.on('chat',function(data){var room=getPlayerRoom(socket.id);if(!room)return;var p=room.players.get(socket.id);if(!p)return;var text=(data.text||'').substring(0,100).trim();if(!text)return;io.to(room.code).emit('chat_msg',{name:p.name,text:text,id:socket.id});});

  socket.on('respawn',function(){var room=getPlayerRoom(socket.id);if(!room)return;var p=room.players.get(socket.id);if(!p)return;var sx=(Math.random()-.5)*20,sz=(Math.random()-.5)*20;p.x=sx;p.y=gH(sx,sz);p.z=sz;p.health=100;p.hunger=100;p.isDead=false;io.to(room.code).emit('player_respawned',{id:socket.id,player:pNet(p)});});

  socket.on('disconnect',function(){leaveRoom(socket.id);console.log('[DISCONNECT] '+socket.id);});
});

var PORT=process.env.PORT||3000;
server.listen(PORT,function(){console.log('[SERVER] Running on port '+PORT);});
