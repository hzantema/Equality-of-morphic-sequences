program g (input,output);
var i,j,k,n : integer;
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
pp(i,i,3);
pp(i,3,i);
pp(i,i,3);pp(i,3,i);
end;

procedure expand(i,q:integer);
var c : char;
j,k,m,mm : integer;
hib : array[0..9] of integer;
t : array[0..9,1..25] of byte;
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

writeln('We will prove the following properties simultaneously by induction on n.'); 
for i := 0 to 9 do
if (i=0) or (p[i] > 0) then
begin
write('(',i,') tau(f^{n-1}(');
for j := 1 to len[2,i] do f[3,i,j] := ff[1,p[i]+j];
for j := 1 to len[2,i] do write(f[3,i,j]);
writeln(')) = rho(g^n(',i,'))');
len[3,i] := len[2,i];
end;
writeln('Then our claim follows from (0).'); 

{check basis:}
writeln('Basis n=1 of induction:'); 
for i := 0 to 9 do
if (i=0) or (p[i] > 0) then
begin
for j := 1 to len[2,i] do
if tau[1,f[3,i,j]] <> tau[2,f[2,i,j]] then begin fout := true; writeln('****** error in tau'); end;
write('tau(f^0(');
for j := 1 to len[2,i] do write(f[3,i,j]); 
write(')) = ');
for j := 1 to len[2,i] do write(tau[1,f[3,i,j]]); 
writeln(' = rho(g(',i,'))');
end;
if not fout then writeln('basis of induction proved');
{check induction step:}
for i := 0 to 9 do
if (i=0) or (p[i] > 0) then
begin
writeln('Induction step part (',i,'):'); 
write('tau(f^n(');
for j := 1 to len[2,i] do write(f[3,i,j]);
writeln(')) = ');
write('tau(f^{n-1}(');
for j := 1 to len[2,i] do 
for k := 1 to len[1,f[3,i,j]] do write(f[1,f[3,i,j],k]);
writeln(')) = ');
write('rho(g^n(');
for j := 1 to len[2,i] do write(f[2,i,j]);
writeln(')) = rho(g^{n+1}(',i,'))');

hib[1] := 1;
ff[1,1] := i;
pp(3,1,2);
pp(1,2,3); {F(u_i) stored in 3}
hib[1] := 1;
ff[1,1] := i;
pp(2,1,2);
pp(3,2,1); {u(G(i)) stored in 1}
if hib[1] <> hib[3]  then begin fout := true; writeln('****** error: wrong length in induction step at ',i); end;
if not fout then
for j := 1 to hib[1] do if ff[1,j] <> ff[3,j] then begin fout := true; writeln('****** error in induction step at ',i); end;
end;
if not fout then writeln('Induction step proved, hence claim proved');

end.

