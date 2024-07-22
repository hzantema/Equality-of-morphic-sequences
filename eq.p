program g (input,output);
var i,j,k,t,n,chib : integer;
fout : boolean;
s : string;
f : array[1..3,0..9,1..25] of byte;
len : array[1..3,0..9] of integer;
tau : array[1..2,0..9] of byte;
ff : array[1..3,1..1000] of byte;
hib : array[1..3] of integer;
p : array[0..9] of integer;
dim : array[1..2] of integer;
rate : array[1..2] of real;
a : array[1..2,0..9,0..9] of integer;
c : array[1..2,1..10,1..50] of byte;
ck : array[1..10,1..50] of boolean;
lenc : array[1..10] of integer;

procedure pp(m,ss,tt : integer);
var i,j : integer;
begin
hib[tt] := 0;
for i := 1 to hib[ss] do
for j := 1 to len[m,ff[ss,i]] do
if hib[tt] < 1000 then
begin
if m = 2 then
if ff[ss,i] > 0 then
if p[ff[ss,i]] = 0 then p[ff[ss,i]] := hib[tt];
hib[tt] := hib[tt]+1;
ff[tt,hib[tt]] := f[m,ff[ss,i],j];
end;
end;

function comprate(i:integer):real;
var j,k,m : integer;
t : real;
b : array[0..9,0..9] of real;
r : array[8..9] of real;
begin
b[0,0] := 1;
for j := 1 to dim[i]-1 do b[0,j] := 0;
for m := 1 to 9 do
for j := 0 to dim[i]-1 do
begin
b[m,j] := 0;
for k := 0 to dim[i]-1 do b[m,j] := b[m,j]+b[m-1,k]*a[i,k,j];
end;
for j := 8 to 9 do
begin
t := 0;
for k := 0 to dim[i]-1 do t := t+b[j,k];
r[j] := t;
end;
comprate := r[9]/r[8];
end;

procedure build(i:integer);
begin
hib[i] := 1;
ff[i,1] := 0;
pp(i,i,3);
pp(i,3,i);
pp(i,i,3);
pp(i,3,i);
pp(i,i,3);pp(i,3,i);
end;

procedure expand(i,q:integer);
var c : char;
j,k,m,mm : integer;
hib : array[0..9] of integer;
t : array[0..9,1..50] of byte;
begin
if i=1 then c := 'f' else c := 'g';
writeln('Replace ',c,' by ',c,'^',q,':');
for j := 0 to dim[i]-1 do
begin
write(c,'(',j,') = ');
hib[j] := 0;
for k := 1 to len[i,j] do
for m := 1 to len[i,f[i,j,k]] do 
if q = 2 then
begin hib[j] := hib[j]+1; t[j,hib[j]] := f[i,f[i,j,k],m]; write(t[j,hib[j]]); end
else
for mm := 1 to len[i,f[i,f[i,j,k],m]] do 
begin hib[j] := hib[j]+1; t[j,hib[j]] := f[i,f[i,f[i,j,k],m],mm]; write(t[j,hib[j]]); end;
writeln;
end;
for j :=  0 to dim[i]-1 do
begin
len[i,j] := hib[j];
for k := 1 to len[i,j] do f[i,j,k] := t[j,k];
end;
if i = 2 then
begin
for j := 0 to 9 do p[j] := 0;
build(i);
end;
end;

procedure adjustrates;
var r: real;
begin
r := ln(rate[1])/ln(rate[2]);
if r > 0.49 then
if r < 0.51 then expand(1,2);
if r > 0.32 then
if r < 0.35 then expand(1,3);
if r > 1.98 then
if r < 2.02 then expand(2,2);
if r > 2.97 then
if r < 3.03 then expand(2,3);
if r > 1.48 then
if r < 1.52 then begin expand(2,3); expand(1,2); end;
if r > 0.66 then
if r < 0.68 then begin expand(2,2); expand(1,3); end;
end;

procedure maak;
var i,j,k,t,bhib,cc : integer;
b : array[1..2,1..1000] of byte;

function tel(s : integer) : integer;
var t : array[1..2] of integer;
i,p : integer;
begin
for i := 1 to 2 do  t[i] := len[i,b[i,s]]; 
p := s;
while t[1] <> t[2] do 
begin
p := p + 1;
for i := 1 to 2 do  t[i] := t[i] + len[i,b[i,p]]; 
end;
tel := p;
end;{tel}

procedure voegtoe(p,q : integer);
var i,j : integer;
found : boolean;
begin
found := false;
for i := 1 to chib do
if not found then
if lenc[i] = q+1-p then
begin
j := 1;
while j <= lenc[i] do 
if ((c[1,i,j] = b[1,p-1+j]) and (c[2,i,j] = b[2,p-1+j])) then j := j+1 else j := 1000;
if j = lenc[i]+1 then found := true;
end;
if not fout then
if not found then
if chib < 10 then
begin
chib := chib+1;
lenc[chib] := q+1-p;
for i := 1 to 2 do
for j := p to q do c[i,chib,j+1-p] := b[i,j];
if q-p > 24 then
begin
writeln('******** string too long in induction hypothesis');
fout := true;
end;
end else 
begin
writeln('******** too many induction hypotheses');
fout := true;
end;
end;{voegtoe}

begin {maak}
for i := 1 to 2 do
begin
for k := 1 to len[i,0] do b[i,k] := f[i,0,k];
bhib := len[i,0];
for j := 2 to len[i,0] do
for k := 1 to len[i,b[i,j]] do
begin bhib := bhib+ 1;b[i,bhib] := f[i,b[i,j],k]; end;
{for j := 1 to bhib do write(b[i,j]);
writeln;}
end;
chib := 1;
t := tel(1);
lenc[chib] := t;
for i := 1 to 2 do
for j := 1 to t do c[i,chib,j] := b[i,j];
cc := 0;
while cc < chib do
begin
cc := cc+1;
for i := 1 to 50 do ck[cc,i] := false;
for i := 1 to 2 do
begin
bhib := 0;
for j := 1 to lenc[cc] do
for k := 1 to len[i,c[i,cc,j]] do
begin bhib := bhib+1; b[i,bhib] := f[i,c[i,cc,j],k]; end;
{for j := 1 to bhib do write(b[i,j]);
writeln;}
end;
t := 1;
while t <= bhib do
begin
k := tel(t);
ck[cc,k] := true;
{for i := t to k do write(b[1,i]);
write(', ');
for i := t to k do write(b[2,i]);
writeln;}
voegtoe(t,k);
t := k+1;
end;
end;
end;{maak}




begin {start program}
for j := 0 to 9 do p[j] := 0;
for i := 1 to 2 do
begin
readln(n); {size signature Fi}
dim[i] := n;
for j := 0 to dim[i] do
for k := 0 to dim[i] do a[i,j,k] := 0;
for j := 0 to n-1 do
begin
if i= 1 then write('f(',j,') = ') else write ('g(',j,') = ');
readln(s);
len[i,j] := length(s);
for k := 1 to len[i,j] do 
begin f[i,j,k] := ord(s[k]) - ord('0'); write(f[i,j,k]); a[i,j,f[i,j,k]] := a[i,j,f[i,j,k]]+1; end;
writeln;
end;
readln(s);
for j := 1 to n do 
begin 
tau[i,j-1] := ord(s[j]) - ord('0');
if i=1 then write('tau') else write('rho');
writeln('(',j-1,') = ',tau[i,j-1]);
end; 
rate[i] := comprate(i);
build(i);
end;
adjustrates;
writeln('Claim to be proved: tau(f^infty(0)) = rho(g^infty(0)).');
{writeln(hib[1]);
writeln(hib[2]);}
fout := false;
for i := 1 to 1000 do
if i <= hib[1] then
if i <= hib[2] then
if tau[1,ff[1,i]] <> tau[2,ff[2,i]] then 
if not fout then 
begin
writeln('****** error on position ',i);
fout := true;
end;
{if not fout then writeln('First part checked to be equal');}
if not fout then 
begin
maak;
writeln('We will prove the following ',chib,' properties simultaneously by induction on n.'); 
for j := 1 to chib do
begin
write('(',j-1,') tau(f^n(');
for i := 1 to lenc[j] do write(c[1,j,i]);
write(')) = rho(g^n(');
for i := 1 to lenc[j] do write(c[2,j,i]);
writeln(')).');
end;
writeln('Then our claim follows from (0).'); 

writeln('Basis n=0 of induction:'); 
for j := 1 to chib do
begin
for i := 1 to lenc[j] do 
if tau[1,c[1,j,i]] <> tau[2,c[2,j,i]] then begin fout := true; writeln('****** error in tau'); end;
write('tau(f^0(');
for i := 1 to lenc[j] do write(c[1,j,i]);
write(')) = ');
for i := 1 to lenc[j] do write(tau[1,c[1,j,i]]);
write(' = rho(g^0(');
for i := 1 to lenc[j] do write(c[2,j,i]);
writeln(')).');
end;
if not fout then writeln('Basis of induction proved.');
if not fout then
for j := 1 to chib do
begin
writeln('Induction step part (',j-1,'):'); 
write('tau(f^{n+1}(');
for i := 1 to lenc[j] do write(c[1,j,i]);
writeln(')) = ');
write('tau(f^n(f(');
for i := 1 to lenc[j] do write(c[1,j,i]);
writeln('))) = ');
write('tau(f^n(');
for i := 1 to lenc[j] do 
for k := 1 to len[1,c[1,j,i]] do  write(f[1,c[1,j,i],k]);
writeln(')) = ');
t := 0;
write('tau(f^n(');
for i := 1 to lenc[j] do 
for k := 1 to len[1,c[1,j,i]] do 
begin 
t := t + 1; 
if ck[j,t-1] then write(')) tau(f^n(',f[1,c[1,j,i],k]) else write(f[1,c[1,j,i],k]); 
end;
writeln(')) =   (by induction hypothesis)');
t := 0;
write('rho(g^n(');
for i := 1 to lenc[j] do 
for k := 1 to len[2,c[2,j,i]] do 
begin 
t := t + 1; 
if ck[j,t-1] then write(')) rho(g^n(',f[2,c[2,j,i],k]) else write(f[2,c[2,j,i],k]); 
end;
writeln(')) = ');
write('rho(g^n(');
for i := 1 to lenc[j] do 
for k := 1 to len[2,c[2,j,i]] do write(f[2,c[2,j,i],k]); 
writeln(')) = ');
write('rho(g^n(g(');
for i := 1 to lenc[j] do write(c[2,j,i]);
writeln('))) = ');
write('rho(g^{n+1}(');
for i := 1 to lenc[j] do write(c[2,j,i]);
writeln(')).');
end;
if not fout then writeln('Induction step proved, hence claim proved.');
end;
end.

