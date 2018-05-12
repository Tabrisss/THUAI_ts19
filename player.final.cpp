#include"communication.h"
#include<vector>
#include<iostream>
#include<ctime>
#pragma warning(disable:4996)
using namespace std;

extern State* state;
extern std::vector<State* > all_state;
extern int** ts19_map;
extern bool ts19_flag;

clock_t start,finish,duration;
void selllist_for_defence();
void selllist_for_Von(int n);
void selllist_for_VonAdd(int n);
void selllist_for_NortonTony(int n);
void selllist_for_TheveninKao(int n);
void selllist_for_Musk(int n);
void antifastattack_selllist();

//——————————工具——————————

struct Defence{
	float enemy_soldier[8];
	float criticalpoint;
	int enemy_mode;
	float own_defence;
	float Bitdefence;
	float THNdefence;
	float Hawkincount;
	int Static_Larry;
};
struct battlemessage{
	int attackmode;
	int defencemode;
	float turnresource_count;
	float turnbuildingpoint_count;
	int building_count;
	vector<Position> build_this_turn;
	vector<Position> placed;
	vector<Building> selllist;
	int sellup;
	int own_road_camp[8][8];
	int ENIAC_line[16];
	int ENIAC_lineAdd[8];
	Defence Road[8];
} Message;
vector<Position> protectlist;

//计算两坐标距离
int dist(Position p1, Position p2)
{return (abs(p1.x - p2.x)+abs(p1.y - p2.y));}

//判断建造是否合法
inline bool able_to_build (Position p)
{
	if ( p.x >= 200 || p.x < 0 || p.y >= 200 || p.y < 0 ) return 0;
	if ( ts19_map[p.x][p.y] )	return 0;//非空地不能建造

	bool f=0;
	for (int i=0;i<Message.build_this_turn.size();i++){
		if ( dist(p,Message.build_this_turn[i]) < 6 ) return 0;
		else if ( dist(p,Message.build_this_turn[i] ) <= 10 ) f=1;
	}
	for (int i=0;i<state->building[!ts19_flag].size();i++) {
		if ( dist(p,state->building[!ts19_flag][i].pos) < 6 ) return 0;}
	for (int i=0;i<state->building[ts19_flag].size();i++) {
		if ( dist(p,state->building[ts19_flag][i].pos) < 6 ) return 0;
		else if ( dist(p,state->building[ts19_flag][i].pos) <= 10 || 
			( !ts19_flag && p.x < 11 && p.y < 11 ) || (ts19_flag && p.x > 188 && p.y > 188) ) f=1;
	}
	return f;
}

//——————————地图重绘——————————

//绘制路标号的地图
int road_mark_map[200][200]={0};
int road_count=0;//用来统计路数
vector<Position> road_block[8];//road_block的1-7下标，对应存放一条路上全体格子的坐标
void markroad0(int,int,int);
void markroad1(int,int,int);

//建立标路径号的地图，同时在每次标号时，都把当前坐标存到第i条路的vector中，统一第n块砖在n线
void road_mark_map_set0(){//从左到右
	for(int i=0;i<=7;i++){
		if(ts19_map[7][i]==1&&road_mark_map[7][i]==0){
			road_count++;
			for (int t=0;t<7+i;t++){
				road_block[road_count].push_back(Position(7,i));}
			markroad0(7,i,road_count);}
	}
	for(int j=6;j>=0;j--){
		if(ts19_map[j][7]==1&&road_mark_map[j][7]==0){
			road_count++;
			for (int t=0;t<7+j;t++){
				road_block[road_count].push_back(Position(j,7));}
			markroad0(j,7,road_count);}
	}
}
void road_mark_map_set1(){//从右到左
	for(int i=199;i>=192;i--){
		if(ts19_map[192][i]==1&&road_mark_map[192][i]==0){
			road_count++;
			for (int t=0;t<7+199-i;t++){
				road_block[road_count].push_back(Position(192,i));}
			markroad1(192,i,road_count);}
	}
	for(int j=193;j<=199;j++){
		if(ts19_map[j][192]==1&&road_mark_map[j][192]==0){
			road_count++;
			for (int t=0;t<7+199-j;t++){
				road_block[road_count].push_back(Position(j,192));}
			markroad1(j,192,road_count);}
	}
}
void markroad0(int x,int y,int num)
{
	if ( x+y>=300 ) return;
	road_mark_map[x][y]=num;road_block[num].push_back(Position(x,y));
	if ( x<=199 && ts19_map[x+1][y]==1 && road_mark_map[x+1][y]==0 ) markroad0(x+1,y,num);
	else if ( y<=199 && ts19_map[x][y+1]==1 && road_mark_map[x][y+1]==0 ) markroad0(x,y+1,num);
	else return;
}
void markroad1(int x,int y,int num)
{
	if ( x+y<=98 ) return;
	road_mark_map[x][y]=num;road_block[num].push_back(Position(x,y));
	if ( x>=0 && ts19_map[x-1][y]==1 && road_mark_map[x-1][y]==0 ) markroad1(x-1,y,num);
	else if ( y>=0 && ts19_map[x][y-1]==1 && road_mark_map[x][y-1]==0 ) markroad1(x,y-1,num);
	else return;
}

//——————————进攻端——————————

const int line1=220,line2=120,line3=80;

//戴维南/高锟12，冯诺依曼/图灵15，伯纳斯李10，托尼斯塔克8，大个从前往后，小个从后往前
bool camp_map_TheveninKao[8][200][200];
bool camp_map_NortonTony[8][200][200];
vector<Position> camp_TheveninKao_list[8];
vector<Position> camp_ShaLee_list[8];
vector<Position> camp_NortonTony_list[8];
void camp_map_TheveninKao_set0(int n){
	if (!road_block[n].size()) return;
	int r=12;
	for (int s=7;s<=85;s++){
		for (int x=0;x<=s;x++){
			if (ts19_map[x][s-x]) continue;
			for (int i=s;i<=85;i++){
				if ( dist(Position(x,s-x),road_block[n][i]) <= r ) {
					camp_map_TheveninKao[n][x][s-x]=1;camp_TheveninKao_list[n].push_back(Position(x,s-x));break;}
			}
		}
	}
}
void camp_map_TheveninKao_set1(int n){
	if (!road_block[n].size()) return;
	int r=12;
	for (int s=391;s>=313;s--){
		for (int x=199;x>=s-199;x--){
			if (ts19_map[x][s-x]) continue;
			for (int i=398-s;i<=85;i++){
				if ( dist(Position(x,s-x),road_block[n][i]) <= r ) {
					camp_map_TheveninKao[n][x][s-x]=1;camp_TheveninKao_list[n].push_back(Position(x,s-x));break;}
			}
		}
	}
}
void camp_map_ShaLee_set0(int n){
	if (!road_block[n].size()) return;
	int r=10;
	for (int s=10;s<=85;s++){
		for (int x=0;x<=s;x++){
			if (ts19_map[x][s-x]) continue;
			for (int i=s;i<=85;i++){
				if ( dist(Position(x,s-x),road_block[n][i]) <= r ) {
					camp_ShaLee_list[n].push_back(Position(x,s-x));break;}
			}
		}
	}
}
void camp_map_ShaLee_set1(int n){
	if (!road_block[n].size()) return;
	int r=10;
	for (int s=388;s>=313;s--){
		for (int x=199;x>=s-199;x--){
			if (ts19_map[x][s-x]) continue;
			for (int i=398-s;i<=85;i++){
				if ( dist(Position(x,s-x),road_block[n][i]) <= r ) {
					camp_ShaLee_list[n].push_back(Position(x,s-x));break;}
			}
		}
	}
}
void camp_map_NortonTony_set0(int n){
	if (!road_block[n].size()) return;
	int r=8;
	for (int s=85;s>=7;s--){
		for (int x=0;x<=s;x++){
			if (ts19_map[x][s-x]) continue;
			for (int i=s;i<=85;i++){
				if ( dist(Position(x,s-x),road_block[n][i]) <= r ) {
					camp_map_NortonTony[n][x][s-x]=1;camp_NortonTony_list[n].push_back(Position(x,s-x));break;}
			}
		}
	}
}
void camp_map_NortonTony_set1(int n){
	if (!road_block[n].size()) return;
	int r=8;
	for (int s=313;s<=391;s++){
		for (int x=199;x>=s-199;x--){
			if (ts19_map[x][s-x]) continue;
			for (int i=398-s;i<=85;i++){
				if ( dist(Position(x,s-x),road_block[n][i]) <= r ) {
					camp_map_NortonTony[n][x][s-x]=1;camp_NortonTony_list[n].push_back(Position(x,s-x));break;}
			}
		}
	}
}

//集结点寻找函数，参数为兵营位置、兵营半径、路号
Position find_road_forward(Position &p,int r,int n){
	for (int i=road_block[n].size()/3-1;i>=0;i--){
		if ( dist(p,road_block[n][i]) <= r )
			return (road_block[n][i]);}
	return Position(0,0);
}
Position find_road_backward(Position &p,int r,int n){
	for (int i=0;i<road_block[n].size()/3;i++){
		if ( dist(p,road_block[n][i]) <= r ) 
			return (road_block[n][i]);}
	return Position(0,0);
}

//兵营一回合只造一个

//香农
void build_Shannon(int n,int max){
	for (int i=0;i<max;i++){
		if ( Message.turnresource_count < OriginalBuildingAttribute[Shannon][6] ||
			Message.turnbuildingpoint_count < OriginalBuildingAttribute[Shannon][7] ||
			Message.own_road_camp[n][0] >= max ) return;
		if ( Message.building_count >= 39 + 20 * state->age[ts19_flag] ) antifastattack_selllist();
		if ( Message.building_count >= 41 + 20 * state->age[ts19_flag] ) return;
		Position s;
		for (int i=0;i<camp_ShaLee_list[n].size();i++){
			if ( able_to_build(camp_ShaLee_list[n][i]) ) {
				s=camp_ShaLee_list[n][i];break;}
		}
		if ( s.x == -1 )
			return;
		construct(Shannon,s,find_road_forward(s,10,n));
		Message.build_this_turn.push_back(s);
		Message.building_count++;
		Message.own_road_camp[n][0]++;
		Message.turnresource_count -= OriginalBuildingAttribute[Shannon][6];
		Message.turnbuildingpoint_count -= OriginalBuildingAttribute[Shannon][7];
	}
}
//戴维南
void build_Thevenin(int n,int max){
	if ( Message.turnresource_count < OriginalBuildingAttribute[Thevenin][6] ||
		Message.turnbuildingpoint_count < OriginalBuildingAttribute[Thevenin][7] ||
		Message.own_road_camp[n][1] >= max ) return;
	if ( Message.building_count >= 39 + 20 * state->age[ts19_flag] ) antifastattack_selllist();
	if ( Message.building_count >= 41 + 20 * state->age[ts19_flag] ) return;
	Position s;
	for (int i=0;i<camp_TheveninKao_list[n].size();i++){
		if ( able_to_build(camp_TheveninKao_list[n][i]) ) {
			s=camp_TheveninKao_list[n][i];break;}
	}
	if ( s.x == -1 )
		return;
	construct(Thevenin,s,find_road_forward(s,12,n));
	Message.build_this_turn.push_back(s);
	Message.building_count++;
	Message.own_road_camp[n][1]++;
	Message.turnresource_count -= OriginalBuildingAttribute[Thevenin][6];
	Message.turnbuildingpoint_count -= OriginalBuildingAttribute[Thevenin][7];
}
//诺顿
void build_Norton(int n,int max){
	if ( Message.turnresource_count < OriginalBuildingAttribute[Norton][6] ||
		Message.turnbuildingpoint_count < OriginalBuildingAttribute[Norton][7] ||
		Message.own_road_camp[n][2] >= max) return;
	//if ( Message.building_count >= 36 + 20 * state->age[ts19_flag] ) selllist();
	if ( Message.building_count >= 41 + 20 * state->age[ts19_flag] ) return;
	Position s;
	for (int i=0;i<camp_NortonTony_list[n].size();i++){
		if ( able_to_build(camp_NortonTony_list[n][i]) ) {
			s=camp_NortonTony_list[n][i];break;}
	}
	if ( s.x == -1 ) {
		selllist_for_NortonTony(n);return;}
	construct(Norton,s,find_road_forward(s,8,n));
	Message.build_this_turn.push_back(s);
	Message.building_count++;
	Message.own_road_camp[n][2]++;
	Message.turnresource_count -= OriginalBuildingAttribute[Norton][6];
	Message.turnbuildingpoint_count -= OriginalBuildingAttribute[Norton][7];
}
//伯纳斯李
void build_Berners_Lee(int n,int max){
	for (int i=0;i<max;i++){
		if ( Message.turnresource_count < OriginalBuildingAttribute[Berners_Lee][6] ||
			Message.turnbuildingpoint_count < OriginalBuildingAttribute[Berners_Lee][7] ||
			Message.own_road_camp[n][4] >= max) return;
		//if ( Message.building_count >= 36 + 20 * state->age[ts19_flag] ) selllist();
		if ( Message.building_count >= 41 + 20 * state->age[ts19_flag] ) return;
		Position s;
		for (int i=0;i<camp_ShaLee_list[n].size();i++){
			if ( able_to_build(camp_ShaLee_list[n][i]) ) {
				s=camp_ShaLee_list[n][i];break;}
		}
		if ( s.x == -1 ) {
			/*selllist();*/return;}
		construct(Berners_Lee,s,find_road_forward(s,10,n));
		Message.build_this_turn.push_back(s);
		Message.building_count++;
		Message.own_road_camp[n][4]++;
		Message.turnresource_count -= OriginalBuildingAttribute[Berners_Lee][6];
		Message.turnbuildingpoint_count -= OriginalBuildingAttribute[Berners_Lee][7];
	}
}
//高锟
void build_Kuen_Kao(int n,int max){
	for (int i=0;i<max;i++){
		if ( Message.turnresource_count < OriginalBuildingAttribute[Kuen_Kao][6] ||
			Message.turnbuildingpoint_count < OriginalBuildingAttribute[Kuen_Kao][7] ||
			Message.own_road_camp[n][5] >= max) return;
		//if ( Message.building_count >= 36 + 20 * state->age[ts19_flag] ) selllist();
		if ( Message.building_count >= 41 + 20 * state->age[ts19_flag] ) return;
		Position s;
		for (int i=0;i<camp_TheveninKao_list[n].size();i++){
			if ( able_to_build(camp_TheveninKao_list[n][i]) ) {
				s=camp_TheveninKao_list[n][i];break;}
		}
		if ( s.x == -1 ) {
			selllist_for_TheveninKao(n);return;}
		construct(Kuen_Kao,s,find_road_forward(s,12,n));
		Message.build_this_turn.push_back(s);
		Message.building_count++;
		Message.own_road_camp[n][5]++;
		Message.turnresource_count -= OriginalBuildingAttribute[Kuen_Kao][6];
		Message.turnbuildingpoint_count -= OriginalBuildingAttribute[Kuen_Kao][7];
	}
}
//托尼斯塔克
void build_Tony_Stark(int n,int max){
	for (int i=0;i<max;i++){
		if ( Message.turnresource_count < OriginalBuildingAttribute[Tony_Stark][6] ||
			Message.turnbuildingpoint_count < OriginalBuildingAttribute[Tony_Stark][7] ||
			Message.own_road_camp[n][7] >= max) return;
		if ( Message.building_count >= 41 + 20 * state->age[ts19_flag] ) {selllist_for_defence();return;}
		Position s;
		for (int i=0;i<camp_NortonTony_list[n].size();i++){
			if ( able_to_build(camp_NortonTony_list[n][i]) ) {
				s=camp_NortonTony_list[n][i];break;}
		}
		if ( s.x == -1 ) {
			selllist_for_NortonTony(n);return;}
		construct(Tony_Stark,s,find_road_forward(s,8,n));
		Message.build_this_turn.push_back(s);
		Message.building_count++;
		Message.own_road_camp[n][7]++;
		Message.turnresource_count -= OriginalBuildingAttribute[Tony_Stark][6];
		Message.turnbuildingpoint_count -= OriginalBuildingAttribute[Tony_Stark][7];
	}
}

//稳定间隔ENIAC
bool camp_map_Von[16][200][200];
vector<Position> camp_Von_list[16];
void camp_map_Von_set0(){
	int r=15;
	for (int n=0;n<16;n++){
		int d=10+4*n;
		for (int s=85;s>=10;s--){
			for (int x=0;x<=s;x++){
				if (ts19_map[x][s-x]) continue;
				if ( dist(Position(x,s-x),road_block[1][d]) <= r ) {
					camp_map_Von[n][x][s-x]=1;camp_Von_list[n].push_back(Position(x,s-x));}
			}
		}
	}
}
void camp_map_Von_set1(){
	int r=15;
	for (int n=0;n<16;n++){
		int d=10+4*n;
		for (int s=313;s<=388;s++){
			for (int x=199;x>=s-199;x--){
				if (ts19_map[x][s-x]) continue;
				if ( dist(Position(x,s-x),road_block[1][d]) <= r ) {
					camp_map_Von[n][x][s-x]=1;camp_Von_list[n].push_back(Position(x,s-x));}
			}
		}
	}
}
void build_Von_Neumann(){
	for (int n=15;n>=0;n--){
		if ( Message.turnresource_count < OriginalBuildingAttribute[Von_Neumann][6] ||
			Message.turnbuildingpoint_count < OriginalBuildingAttribute[Von_Neumann][7] ) return;
		//if ( Message.building_count >= 36 + 20 * state->age[ts19_flag] ) selllist();
		if ( Message.building_count >= 41 + 20 * state->age[ts19_flag] ) return;
		if ( Message.ENIAC_line[n] ) continue;
		Position s;
		for (int i=0;i<camp_Von_list[n].size();i++){
			if ( able_to_build(camp_Von_list[n][i]) ) {
				s=camp_Von_list[n][i];break;}
		}
		if ( s.x == -1 ) {
			selllist_for_Von(n);return;}
		construct(Von_Neumann,s,road_block[1][10+4*n]);
		Message.build_this_turn.push_back(s);
		Message.building_count++;
		Message.ENIAC_line[n]=1;
		Message.turnresource_count -= OriginalBuildingAttribute[Von_Neumann][6];
		Message.turnbuildingpoint_count -= OriginalBuildingAttribute[Von_Neumann][7];
	}
}
bool camp_map_VonAdd[8][200][200];
vector<Position> camp_VonAdd_list[8];
void camp_map_VonAdd_set0(){
	int r=15;
	for (int n=0;n<8;n++){
		int d=10+8*n;
		for (int s=85;s>=10;s--){
			for (int x=0;x<=s;x++){
				if (ts19_map[x][s-x]) continue;
				if ( dist(Position(x,s-x),road_block[road_count][d]) <= r ) {
					camp_map_VonAdd[n][x][s-x]=1;camp_VonAdd_list[n].push_back(Position(x,s-x));}
			}
		}
	}
}
void camp_map_VonAdd_set1(){
	int r=15;
	for (int n=0;n<8;n++){
		int d=10+8*n;
		for (int s=313;s<=388;s++){
			for (int x=199;x>=s-199;x--){
				if (ts19_map[x][s-x]) continue;
				if ( dist(Position(x,s-x),road_block[road_count][d]) <= r ) {
					camp_map_VonAdd[n][x][s-x]=1;camp_VonAdd_list[n].push_back(Position(x,s-x));}
			}
		}
	}
}
void build_Von_Neumann_Add(){
	for (int n=7;n>=0;n--){
		if ( Message.turnresource_count < OriginalBuildingAttribute[Von_Neumann][6] ||
			Message.turnbuildingpoint_count < OriginalBuildingAttribute[Von_Neumann][7] ) return;
		//if ( Message.building_count >= 36 + 20 * state->age[ts19_flag] ) selllist();
		if ( Message.building_count >= 41 + 20 * state->age[ts19_flag] ) return;
		if ( Message.ENIAC_lineAdd[n] ) continue;
		Position s;
		for (int i=0;i<camp_VonAdd_list[n].size();i++){
			if ( able_to_build(camp_VonAdd_list[n][i]) ) {
				s=camp_VonAdd_list[n][i];break;}
		}
		if ( s.x == -1 ) {
			selllist_for_VonAdd(n);return;}
		construct(Von_Neumann,s,road_block[road_count][10+8*n]);
		Message.build_this_turn.push_back(s);
		Message.building_count++;
		Message.ENIAC_lineAdd[n]=1;
		Message.turnresource_count -= OriginalBuildingAttribute[Von_Neumann][6];
		Message.turnbuildingpoint_count -= OriginalBuildingAttribute[Von_Neumann][7];
	}
}

//————————收集当前回合动态信息————————

vector<Position> Larry_Roberts_list[8];
vector<Position> Hawkin_list[8];
vector<Position> BoolOhm_home_list[8];
vector<Position> BoolOhm_line_list[8];
bool Larry_Roberts_point[8][200][200];
bool Hawkin_point[8][200][200];
bool BoolOhm_home_point[8][200][200];
bool BoolOhm_line_point[8][200][200];

float Max(float a[]){
	float max=0;
	for (int i=0;i<8;i++){
		if ( a[i]>max ) {max=a[i];}
	}
	return max;
}
void enemy_attack_refresh(){
	for (int i=0;i<8;i++){
		for (int j=0;j<8;j++){
			Message.Road[i].enemy_soldier[j]=0;
			Message.Road[i].criticalpoint=0;}
	}
	if (!ts19_flag){
		for (int i=0;i<state->soldier[1].size();i++) {
			int road = road_mark_map[state->soldier[1][i].pos.x][state->soldier[1][i].pos.y];
			if (!road) continue;
			switch (state->soldier[1][i].soldier_name) {
			case 3:case 6:case 7:
				if ( dist(Position(0,0),state->soldier[1][i].pos) <= 250 &&
					Message.Road[road].enemy_soldier[state->soldier[1][i].soldier_name] < state->soldier[1][i].heal ) {
						Message.Road[road].enemy_soldier[state->soldier[1][i].soldier_name] = state->soldier[1][i].heal;}
			case 0:case 1:case 2:case 4:case 5:
				if ( dist(Position(0,0),state->soldier[1][i].pos) <= 180 &&
					Message.Road[road].enemy_soldier[state->soldier[1][i].soldier_name] < state->soldier[1][i].heal ) {
						Message.Road[road].enemy_soldier[state->soldier[1][i].soldier_name] = state->soldier[1][i].heal;}
			}
		}
	}
	else {
		for (int i=0;i<state->soldier[0].size();i++) {
			int road = road_mark_map[state->soldier[0][i].pos.x][state->soldier[0][i].pos.y];
			if (!road) continue;
			switch (state->soldier[0][i].soldier_name) {
			case 3:case 6:case 7:
				if ( dist(Position(199,199),state->soldier[0][i].pos) <= 250 &&
					Message.Road[road].enemy_soldier[state->soldier[0][i].soldier_name] < state->soldier[0][i].heal ) {
						Message.Road[road].enemy_soldier[state->soldier[0][i].soldier_name] = state->soldier[0][i].heal;}
			case 0:case 1:case 2:case 4:case 5:
				if ( dist(Position(199,199),state->soldier[0][i].pos) <= 180 &&
					Message.Road[road].enemy_soldier[state->soldier[0][i].soldier_name] < state->soldier[0][i].heal ) {
						Message.Road[road].enemy_soldier[state->soldier[0][i].soldier_name] = state->soldier[0][i].heal;}
			}
		}
	}

	for (int n=1;n<=road_count;n++) {
		Message.Road[n].enemy_soldier[2] *= 2;
		Message.Road[n].enemy_soldier[4] *= 0.8;
		if ( Message.Road[n].enemy_soldier[0] + Message.Road[n].enemy_soldier[1] + Message.Road[n].enemy_soldier[2] + 
			Message.Road[n].enemy_soldier[3] + Message.Road[n].enemy_soldier[4] + Message.Road[n].enemy_soldier[5] + 
			Message.Road[n].enemy_soldier[6] + Message.Road[n].enemy_soldier[7] == 0 ) {
				Message.Road[n].enemy_mode=0;
				Message.Road[n].criticalpoint=0;}
		else if ( Message.Road[n].enemy_soldier[0] + Message.Road[n].enemy_soldier[1] + Message.Road[n].enemy_soldier[2] +
			Message.Road[n].enemy_soldier[4] + Message.Road[n].enemy_soldier[5] == 0 ) {
				Message.Road[n].enemy_mode=1;
				Message.Road[n].criticalpoint=0;
		}
		else if ( Message.Road[n].enemy_soldier[3] + Message.Road[n].enemy_soldier[6] + Message.Road[n].enemy_soldier[7] == 0 ) {
			Message.Road[n].enemy_mode=2;
			Message.Road[n].criticalpoint=1.5*Max(Message.Road[n].enemy_soldier);
		}
		else {
			Message.Road[n].enemy_mode=3;
			Message.Road[n].enemy_soldier[3]=0;Message.Road[n].enemy_soldier[6]=0;Message.Road[n].enemy_soldier[7]=0;
			Message.Road[n].criticalpoint=1.5*Max(Message.Road[n].enemy_soldier);
		}
	}
}
void enemy_fastattack_refresh(){
	for (int i=0;i<8;i++){
		for (int j=0;j<8;j++){
			Message.Road[i].enemy_soldier[j]=0;
			Message.Road[i].criticalpoint=0;}
	}

	if (!ts19_flag){
		for (int i=0;i<state->soldier[1].size();i++) {
			int road = road_mark_map[state->soldier[1][i].pos.x][state->soldier[1][i].pos.y];
			if (!road) continue;
			if ( dist(Position(0,0),state->soldier[1][i].pos) <= line1 ) {
				Message.Road[road].enemy_soldier[state->soldier[1][i].soldier_name] += state->soldier[1][i].heal;}
		}
	}
	else {
		for (int i=0;i<state->soldier[0].size();i++) {
			int road = road_mark_map[state->soldier[0][i].pos.x][state->soldier[0][i].pos.y];
			if (!road) continue;
			if ( dist(Position(199,199),state->soldier[0][i].pos) <= line1 ) {
				Message.Road[road].enemy_soldier[state->soldier[0][i].soldier_name] += state->soldier[0][i].heal;}
		}
	}
	if ( Message.defencemode < 0 ) {
		for (int n=1;n<=road_count;n++){
			Message.Road[n].enemy_soldier[0] *= 2.5;
			Message.Road[n].enemy_soldier[1] *= 1.8;
			Message.Road[n].enemy_soldier[2] *= 1.5;
		}
	}
}
int Larry_weight_map[200][200]={0};
int Hawkin_weight_map[200][200]={0};
void enemyattack_weight_map_refresh(){
	for (int i=0;i<200;i++){
		for (int j=0;j<200;j++){
			Larry_weight_map[i][j]=0;
			Hawkin_weight_map[i][j]=0;}
	}
	for (int n=1;n<=road_count;n++){
		if ( Message.Road[n].enemy_mode ) {
			for (int i=0;i<200;i++){
				for (int j=0;j<200;j++){
					Larry_weight_map[i][j] += Larry_Roberts_point[n][i][j];
					Hawkin_weight_map[i][j] += Hawkin_point[n][i][j];}
			}
		}
	}	
}
void defence_refresh(Building bd){
	for (int n=1;n<=road_count;n++){
		if ( bd.building_type==13 && Larry_Roberts_point[n][bd.pos.x][bd.pos.y] && Larry_weight_map[bd.pos.x][bd.pos.y] ) {
			Message.Road[n].own_defence += (float) OriginalBuildingAttribute[13][2] * (1+0.5*bd.level) 
				/ Larry_weight_map[bd.pos.x][bd.pos.y] ;}
		else if ( bd.building_type==16 && Hawkin_point[n][bd.pos.x][bd.pos.y] && Hawkin_weight_map[bd.pos.x][bd.pos.y]) {
			Message.Road[n].Hawkincount += (float) 1 / Hawkin_weight_map[bd.pos.x][bd.pos.y];
		}
	}
}
void defence_refresh_update(Building bd){
	for (int n=1;n<=road_count;n++){
		if ( bd.building_type==13 && Larry_Roberts_point[n][bd.pos.x][bd.pos.y] && Larry_weight_map[bd.pos.x][bd.pos.y] ) {
			Message.Road[n].own_defence += 0.5 * OriginalBuildingAttribute[13][2] 
			/ Larry_weight_map[bd.pos.x][bd.pos.y] ;}
	}
}
void antifastattack_defence_refresh(Building bd){
	float distru_ratio[8]={0};
	float sum=0;
	if ( bd.building_type == 9 ) {
		for (int n=1;n<=road_count;n++) {
			if ( BoolOhm_home_point[n][bd.pos.x][bd.pos.y] + BoolOhm_line_point[n][bd.pos.x][bd.pos.y] ) {
				sum += Message.Road[n].enemy_soldier[0];}
		}
		if (!sum) return;
		for (int n=1;n<=road_count;n++) {
			if ( BoolOhm_home_point[n][bd.pos.x][bd.pos.y] + BoolOhm_line_point[n][bd.pos.x][bd.pos.y] ) {
				distru_ratio[n] = Message.Road[n].enemy_soldier[0] / sum;
				Message.Road[n].Bitdefence += (float) OriginalBuildingAttribute[9][2] * (1+0.5*bd.level) * distru_ratio[n];}
		}
	}
	else if ( bd.building_type == 10 ) {
		for (int n=1;n<=road_count;n++) {
			if ( BoolOhm_home_point[n][ bd.pos.x][bd.pos.y] + BoolOhm_line_point[n][bd.pos.x][bd.pos.y] ) {
				sum += Message.Road[n].enemy_soldier[1] + Message.Road[n].enemy_soldier[2];}
		}
		if (!sum) return;
		for (int n=1;n<=road_count;n++) {
			if ( BoolOhm_home_point[n][bd.pos.x][bd.pos.y] + BoolOhm_line_point[n][bd.pos.x][bd.pos.y] ) {
				distru_ratio[n] = ( Message.Road[n].enemy_soldier[1] + Message.Road[n].enemy_soldier[2] ) / sum;
				Message.Road[n].THNdefence += (float) OriginalBuildingAttribute[10][2] * (1+0.5*bd.level) * distru_ratio[n] ;
			}
		}
	}
	//把防御塔的全额伤害，按敌方各路兵力分布情况分配到各路防御
}

//回合开始时刷新Message信息
void message_refresh(){
	Message.turnresource_count=state->resource[ts19_flag].resource;
	Message.turnbuildingpoint_count=state->resource[ts19_flag].building_point;
	Message.building_count=state->building[ts19_flag].size();
	vector<Position> tmp1;
	Message.build_this_turn.swap(tmp1);
	vector<Building> tmp2;
	Message.selllist.swap(tmp2);

	if ( state->age[ts19_flag] < 2 ) {//0、1代防偷家
		if (!ts19_flag){
			int mindist=181;Position minpos;
			for (int i=0;i<state->building[!ts19_flag].size();i++) {
				if ( dist( state->building[!ts19_flag][i].pos,Position(0,0) ) < mindist ) {
					mindist = dist( state->building[!ts19_flag][i].pos,Position(0,0) );
					minpos = state->building[!ts19_flag][i].pos;}
			}
			if ( mindist <= 180 ) {
				if ( minpos.x > minpos.y ) Message.defencemode=-1;
				else Message.defencemode=-2;
			}
		}
		else {
			int mindist=181;Position minpos;
			for (int i=0;i<state->building[!ts19_flag].size();i++) {
				if ( dist( state->building[!ts19_flag][i].pos,Position(199,199) ) < mindist ) {
					mindist = dist( state->building[!ts19_flag][i].pos,Position(199,199) );
					minpos = state->building[!ts19_flag][i].pos;}
			}
			if ( mindist <= 180 ) {
				if ( minpos.x < minpos.y ) Message.defencemode=-1;
				else Message.defencemode=-2;
			}
		}
		if ( Message.defencemode ) enemy_fastattack_refresh();
	}
	else if ( state->age[ts19_flag] < 4 ) {//2、3、4代防速攻
		if ( Message.defencemode == 0 ) {
			for (int i=0;i<state->building[!ts19_flag].size()-1;i++) {
				if ( state->building[!ts19_flag][i].building_type < 4 ) { Message.defencemode=1;break; }
			}
		}
		if ( Message.defencemode ) enemy_fastattack_refresh();
	}
	else {//5代正面对打
		enemy_attack_refresh();
		enemyattack_weight_map_refresh();
		if ( state->turn >= 500 ){
			if ( state->building[ts19_flag][state->building[ts19_flag].size()-1].heal >= state->building[!ts19_flag][state->building[!ts19_flag].size()-1].heal ) {
				Message.attackmode=0; }
			else { Message.attackmode=2; }
		}
		else if ( state->resource[ts19_flag].resource >= 100000 )	Message.attackmode=2;
		else Message.attackmode=1; 
	}

	for (int i=0;i<8;i++){//刷新防御
		Message.Road[i].own_defence=0;
		Message.Road[i].Hawkincount=0;
		Message.Road[i].Bitdefence=0;
		Message.Road[i].THNdefence=0;
	}
	if ( state->age[ts19_flag] < 4 && Message.defencemode ) {
		for (int i=0;i<state->building[ts19_flag].size();i++) {
			if ( state->building[ts19_flag][i].building_type == 9 || state->building[ts19_flag][i].building_type == 10 ) {
				antifastattack_defence_refresh(state->building[ts19_flag][i]);}
		}
	}
	else {
		for (int i=0;i<state->building[ts19_flag].size();i++) {
			if ( state->building[ts19_flag][i].building_type == 13 || state->building[ts19_flag][i].building_type == 16 ) {
				defence_refresh(state->building[ts19_flag][i]);}
		}
	}

	int t1=Message.ENIAC_line[15];
	for (int i=15;i;i--) {
		Message.ENIAC_line[i]=Message.ENIAC_line[i-1];}
	Message.ENIAC_line[0]=t1;
	int t2=Message.ENIAC_lineAdd[7];
	for (int i=7;i;i--) {
		Message.ENIAC_lineAdd[i]=Message.ENIAC_lineAdd[i-1];}
	Message.ENIAC_lineAdd[0]=t2;
}

//——————————防御端——————————

void Larry_Roberts_point_set(int n){
	if (!road_block[n].size()) return;
	int r=40;
	if (road_count==7) {
		if (!ts19_flag) {
			for (int s=line2;s>=line2-25;s--){
				for (int x=20;x<=line2-20;x++){
					int count=0;
					if (ts19_map[x][s-x]) continue;
					for (int i=140;i<200;i++){
						if ( dist(Position(x,s-x),road_block[n][i]) <= r ) count++;
						if ( count >= 18 ) {
							Larry_Roberts_point[n][x][s-x]=1;Larry_Roberts_list[n].push_back(Position(x,s-x));break;}
					}
				}
			}
		}
		else {
			for (int s=398-line2;s<=423-line2;s++){
				for (int x=179;x>=219-line2;x--){
					int count=0;
					if (ts19_map[x][s-x]) continue;
					for (int i=140;i<200;i++){
						if ( dist(Position(x,s-x),road_block[n][i]) <= r ) count++;
						if ( count >= 18 ) {
							Larry_Roberts_point[n][x][s-x]=1;Larry_Roberts_list[n].push_back(Position(x,s-x));break;}
					}
				}
			}
		}
	}
	else {
		if (!ts19_flag){
			for (int s=line2;s>=line2-25;s--){
				for (int x=0;x<=s;x++){
					int count=0;
					if (ts19_map[x][s-x]) continue;
					for (int i=140;i<200;i++){
						if ( dist(Position(x,s-x),road_block[n][i]) <= r ) count++;
						if ( count >= 18 ) {
							Larry_Roberts_point[n][x][s-x]=1;Larry_Roberts_list[n].push_back(Position(x,s-x));break;}
					}
				}
			}
		}
		else {
			for (int s=398-line2;s<=423-line2;s++){
				for (int x=199;x>=s-199;x--){
					int count=0;
					if (ts19_map[x][s-x]) continue;
					for (int i=140;i<200;i++){
						if ( dist(Position(x,s-x),road_block[n][i]) <= r ) count++;
						if ( count >= 18 ) {
							Larry_Roberts_point[n][x][s-x]=1;Larry_Roberts_list[n].push_back(Position(x,s-x));break;}
					}
				}
			}
		}
	}
}
void Hawkin_point_set(int n){
	if (!road_block[n].size()) return;
	int r=20;
	if (road_count==7){
		if (!ts19_flag){
			for (int s=line2+7;s>=line2-10;s--){
				for (int x=22;x<=line2-15;x++){
					int count=0;
					if (ts19_map[x][s-x]) continue;
					for (int i=130;i<200;i++){
						if ( dist(Position(x,s-x),road_block[n][i]) <= r ) count++;
						if ( count >= 10 ) {
							Hawkin_point[n][x][s-x]=1;Hawkin_list[n].push_back(Position(x,s-x));break;}
					}
				}
			}
		}
		else {
			for (int s=391-line2;s<=408-line2;s++){
				for (int x=177;x>=214-line2;x--){
					int count=0;
					if (ts19_map[x][s-x]) continue;
					for (int i=130;i<200;i++){
						if ( dist(Position(x,s-x),road_block[n][i]) <= r ) count++;
						if ( count >= 10 ) {
							Hawkin_point[n][x][s-x]=1;Hawkin_list[n].push_back(Position(x,s-x));break;}
					}
				}
			}
		}
	}
	else {
		if (!ts19_flag){
			for (int s=line2+7;s>=line2-10;s--){
				for (int x=0;x<=s;x++){
					int count=0;
					if (ts19_map[x][s-x]) continue;
					for (int i=130;i<200;i++){
						if ( dist(Position(x,s-x),road_block[n][i]) <= r ) count++;
						if ( count >= 10 ) {
							Hawkin_point[n][x][s-x]=1;Hawkin_list[n].push_back(Position(x,s-x));break;}
					}
				}
			}
		}
		else {
			for (int s=391-line2;s<=408-line2;s++){
				for (int x=199;x>=s-199;x--){
					int count=0;
					if (ts19_map[x][s-x]) continue;
					for (int i=130;i<200;i++){
						if ( dist(Position(x,s-x),road_block[n][i]) <= r ) count++;
						if ( count >= 10 ) {
							Hawkin_point[n][x][s-x]=1;Hawkin_list[n].push_back(Position(x,s-x));break;}
					}
				}
			}
		}
	}
}
void BoolOhm_home_point_set(int n){
	if (!road_block[n].size()) return;
	int r=30;
	if (!ts19_flag){
		for (int s=48;s>=10;s--){
			for (int x=0;x<=s;x++){
				int count=0;
				if (ts19_map[x][s-x]) continue;
				for (int i=80;i;i--){
					if ( dist(Position(x,s-x),road_block[n][i]) <= r ) count++;
					if ( count >= 30 ) {
						BoolOhm_home_point[n][x][s-x]=1;BoolOhm_home_list[n].push_back(Position(x,s-x));break;}
				}
			}
		}
	}
	else {
		for (int s=350;s<=388;s++){
			for (int x=199;x>=s-199;x--){
				int count=0;
				if (ts19_map[x][s-x]) continue;
				for (int i=80;i;i--){
					if ( dist(Position(x,s-x),road_block[n][i]) <= r ) count++;
					if ( count >= 30 ) {
						BoolOhm_home_point[n][x][s-x]=1;BoolOhm_home_list[n].push_back(Position(x,s-x));break;}
				}
			}
		}
	}
}
void BoolOhm_line_point_set(int n){
	if (!road_block[n].size()) return;
	int r=30;
	if (!ts19_flag){
		for (int s=100;s>=60;s--){
			for (int x=0;x<=s;x++){
				int count=0;
				if (ts19_map[x][s-x]) continue;
				for (int i=60;i<150;i++){
					if ( dist(Position(x,s-x),road_block[n][i]) <= r ) count++;
					if ( count >= 45 ) {
						BoolOhm_line_point[n][x][s-x]=1;BoolOhm_line_list[n].push_back(Position(x,s-x));break;}
				}
			}
		}
	}
	else {
		for (int s=308;s<=338;s++){
			for (int x=199;x>=s-199;x--){
				int count=0;
				if (ts19_map[x][s-x]) continue;
				for (int i=60;i<150;i++){
					if ( dist(Position(x,s-x),road_block[n][i]) <= r ) count++;
					if ( count >= 45 ) {
						BoolOhm_line_point[n][x][s-x]=1;BoolOhm_line_list[n].push_back(Position(x,s-x));break;}
				}
			}
		}
	}
}
void Larry_Roberts_point_set1(int n){
	if (!road_block[n].size()) return;
	int r=40;
	if (!ts19_flag){
		for (int x=line2-20;x>=line2-50;x--){
			for (int y=20;y>=0;y--){
				int count=0;
				if (ts19_map[x][y]) continue;
				for (int i=60;i<200;i++){
					if ( dist(Position(x,y),road_block[n][i]) <= r ) count++;
					if ( count >= 60 ) {
						Larry_Roberts_point[n][x][y]=1;Larry_Roberts_list[n].push_back(Position(x,y));break;}
				}
			}
		}
	}
	else {
		for (int x=219-line2;x<=249-line2;x++){
			for (int y=179;y<=199;y++){
				int count=0;
				if (ts19_map[x][y]) continue;
				for (int i=60;i<200;i++){
					if ( dist(Position(x,y),road_block[n][i]) <= r ) count++;
					if ( count >= 60 ) {
						Larry_Roberts_point[n][x][y]=1;Larry_Roberts_list[n].push_back(Position(x,y));break;}
				}
			}
		}
	}
}
void Larry_Roberts_point_set7(int n){
	if (!road_block[n].size()) return;
	int r=40;
	if (!ts19_flag){
		for (int y=line2-20;y>=line2-50;y--){
			for (int x=20;x>=0;x--){
				int count=0;
				if (ts19_map[x][y]) continue;
				for (int i=60;i<200;i++){
					if ( dist(Position(x,y),road_block[n][i]) <= r ) count++;
					if ( count >= 60 ) {
						Larry_Roberts_point[n][x][y]=1;Larry_Roberts_list[n].push_back(Position(x,y));break;}
				}
			}
		}
	}
	else {
		for (int y=219-line2;y<=249-line2;y++){
			for (int x=179;x<=199;x++){
				int count=0;
				if (ts19_map[x][y]) continue;
				for (int i=60;i<200;i++){
					if ( dist(Position(x,y),road_block[n][i]) <= r ) count++;
					if ( count >= 60 ) {
						Larry_Roberts_point[n][x][y]=1;Larry_Roberts_list[n].push_back(Position(x,y));break;}
				}
			}
		}
	}
}
void Hawkin_point_set1(int n){
	if (!road_block[n].size()) return;
	int r=20;
	if (!ts19_flag){
		for (int x=line2-15;x>=line2-30;x--){
			for (int y=22;y>=0;y--){
				int count=0;
				if (ts19_map[x][y]) continue;
				for (int i=105;i<200;i++){
					if ( dist(Position(x,y),road_block[n][i]) <= r ) count++;
					if ( count >= 10 ) {
						Hawkin_point[n][x][y]=1;Hawkin_list[n].push_back(Position(x,y));break;}
				}
			}
		}
	}
	else {
		for (int x=214-line2;x<=229-line2;x++){
			for (int y=177;y<=199;y++){
				int count=0;
				if (ts19_map[x][y]) continue;
				for (int i=105;i<200;i++){
					if ( dist(Position(x,y),road_block[n][i]) <= r ) count++;
					if ( count >= 10 ) {
						Hawkin_point[n][x][y]=1;Hawkin_list[n].push_back(Position(x,y));break;}
				}
			}
		}
	}
}
void Hawkin_point_set7(int n){
	if (!road_block[n].size()) return;
	int r=20;
	if (!ts19_flag){
		for (int y=line2-15;y>=line2-30;y--){
			for (int x=22;x>=0;x--){
				int count=0;
				if (ts19_map[x][y]) continue;
				for (int i=105;i<200;i++){
					if ( dist(Position(x,y),road_block[n][i]) <= r ) count++;
					if ( count >= 10 ) {
						Hawkin_point[n][x][y]=1;Hawkin_list[n].push_back(Position(x,y));break;}
				}
			}
		}
	}
	else {
		for (int y=214-line2;y<=229-line2;y++){
			for (int x=177;x<=199;x++){
				int count=0;
				if (ts19_map[x][y]) continue;
				for (int i=105;i<200;i++){
					if ( dist(Position(x,y),road_block[n][i]) <= r ) count++;
					if ( count >= 10 ) {
						Hawkin_point[n][x][y]=1;Hawkin_list[n].push_back(Position(x,y));break;}
				}
			}
		}
	}
}

//布尔
void build_home_Bool(int n){
	for (int i=0;i<8;i++){
		if ( Message.Road[n].Bitdefence >= Message.Road[n].enemy_soldier[0] ) return;
		if ( Message.turnresource_count < OriginalBuildingAttribute[Bool][6] ||
			Message.turnbuildingpoint_count < OriginalBuildingAttribute[Bool][7] ) return;
		if ( Message.building_count >= 40 + 20 * state->age[ts19_flag] ) antifastattack_selllist();
		if ( Message.building_count >= 41 + 20 * state->age[ts19_flag] ) return;
		Position s;
		for (int t=0;t<BoolOhm_home_list[n].size();t++){
			if ( able_to_build(BoolOhm_home_list[n][t]) ) {
				s=BoolOhm_home_list[n][t];break;}
		}
		if ( s.x == -1 ) 
			return;
		construct(Bool,s);
		Building bd(Bool,OriginalBuildingAttribute[Bool][1],s,ts19_flag,0,0);
		Message.build_this_turn.push_back(bd.pos);Message.building_count++;
		Message.turnresource_count -= OriginalBuildingAttribute[Bool][6];
		Message.turnbuildingpoint_count -= OriginalBuildingAttribute[Bool][7];
		antifastattack_defence_refresh(bd);
	}
}
void build_home_Bool(int n,int max){
	for (int i=0;i<max;i++){
		if ( Message.turnresource_count < OriginalBuildingAttribute[Bool][6] ||
			Message.turnbuildingpoint_count < OriginalBuildingAttribute[Bool][7] ) return;
		if ( Message.building_count >= 41 + 20 * state->age[ts19_flag] ) return;
		Position s;
		for (int t=0;t<BoolOhm_home_list[n].size();t++){
			if ( able_to_build(BoolOhm_home_list[n][t]) ) {
				s=BoolOhm_home_list[n][t];break;}
		}
		if ( s.x == -1 ) 
			return;
		construct(Bool,s);
		Building bd(Bool,OriginalBuildingAttribute[Bool][1],s,ts19_flag,0,0);
		Message.build_this_turn.push_back(bd.pos);Message.building_count++;
		Message.turnresource_count -= OriginalBuildingAttribute[Bool][6];
		Message.turnbuildingpoint_count -= OriginalBuildingAttribute[Bool][7];
		//antifastattack_defence_refresh(bd);
	}
}
void build_line_Bool(int n){
	for (int i=0;i<8;i++){
		if ( Message.Road[n].Bitdefence >= Message.Road[n].enemy_soldier[0] ) return;
		if ( Message.turnresource_count < OriginalBuildingAttribute[Bool][6] ||
			Message.turnbuildingpoint_count < OriginalBuildingAttribute[Bool][7] ) return;
		if ( Message.building_count >= 39 + 20 * state->age[ts19_flag] ) antifastattack_selllist();
		if ( Message.building_count >= 41 + 20 * state->age[ts19_flag] ) return;
		Position s;
		for (int t=0;t<BoolOhm_line_list[n].size();t++){
			if ( able_to_build(BoolOhm_line_list[n][t]) ) {
				s=BoolOhm_line_list[n][t];break;}
		}
		if ( s.x == -1 ) 
			return;
		construct(Bool,s);
		Building bd(Bool,OriginalBuildingAttribute[Bool][1],s,ts19_flag,0,0);
		Message.build_this_turn.push_back(bd.pos);Message.building_count++;
		Message.turnresource_count -= OriginalBuildingAttribute[Bool][6];
		Message.turnbuildingpoint_count -= OriginalBuildingAttribute[Bool][7];
		antifastattack_defence_refresh(bd);
	}
}
//欧姆
void build_home_Ohm(int n){
	for (int i=0;i<8;i++){
		if ( Message.Road[n].THNdefence >= Message.Road[n].enemy_soldier[1] &&
			Message.Road[n].THNdefence >= Message.Road[n].enemy_soldier[2] ) return;
		if ( Message.turnresource_count < OriginalBuildingAttribute[Ohm][6] ||
			Message.turnbuildingpoint_count < OriginalBuildingAttribute[Ohm][7] ) return;
		if ( Message.building_count >= 39 + 20 * state->age[ts19_flag] ) antifastattack_selllist();
		if ( Message.building_count >= 41 + 20 * state->age[ts19_flag] ) return;
		Position s;
		for (int t=0;t<BoolOhm_home_list[n].size();t++){
			if ( able_to_build(BoolOhm_home_list[n][t]) ) {
				s=BoolOhm_home_list[n][t];break;}
		}
		if ( s.x == -1 ) 
			return;
		construct(Ohm,s);
		Building bd(Ohm,OriginalBuildingAttribute[Ohm][1],s,ts19_flag,0,0);
		Message.build_this_turn.push_back(bd.pos);Message.building_count++;
		Message.turnresource_count -= OriginalBuildingAttribute[Ohm][6];
		Message.turnbuildingpoint_count -= OriginalBuildingAttribute[Ohm][7];
		antifastattack_defence_refresh(bd);
	}
}
void build_home_Ohm(int n,int max){
	for (int i=0;i<max;i++){
		if ( Message.turnresource_count < OriginalBuildingAttribute[Ohm][6] ||
			Message.turnbuildingpoint_count < OriginalBuildingAttribute[Ohm][7] ) return;
		if ( Message.building_count >= 41 + 20 * state->age[ts19_flag] ) return;
		Position s;
		for (int t=0;t<BoolOhm_home_list[n].size();t++){
			if ( able_to_build(BoolOhm_home_list[n][t]) ) {
				s=BoolOhm_home_list[n][t];break;}
		}
		if ( s.x == -1 ) 
			return;
		construct(Ohm,s);
		Building bd(Ohm,OriginalBuildingAttribute[Ohm][1],s,ts19_flag,0,0);
		Message.build_this_turn.push_back(bd.pos);Message.building_count++;
		Message.turnresource_count -= OriginalBuildingAttribute[Ohm][6];
		Message.turnbuildingpoint_count -= OriginalBuildingAttribute[Ohm][7];
		//antifastattack_defence_refresh(bd);
	}
}
void build_line_Ohm(int n){
	for (int i=0;i<8;i++){
		if ( Message.Road[n].Bitdefence >= Message.Road[n].enemy_soldier[0] ) return;
		if ( Message.turnresource_count < OriginalBuildingAttribute[Ohm][6] ||
			Message.turnbuildingpoint_count < OriginalBuildingAttribute[Ohm][7] ) return;
		if ( Message.building_count >= 39 + 20 * state->age[ts19_flag] ) antifastattack_selllist();
		if ( Message.building_count >= 41 + 20 * state->age[ts19_flag] ) return;
		Position s;
		for (int t=0;t<BoolOhm_line_list[n].size();t++){
			if ( able_to_build(BoolOhm_line_list[n][t]) ) {
				s=BoolOhm_line_list[n][t];break;}
		}
		if ( s.x == -1 ) 
			return;
		construct(Ohm,s);
		Building bd(Ohm,OriginalBuildingAttribute[Ohm][1],s,ts19_flag,0,0);
		Message.build_this_turn.push_back(bd.pos);Message.building_count++;
		Message.turnresource_count -= OriginalBuildingAttribute[Ohm][6];
		Message.turnbuildingpoint_count -= OriginalBuildingAttribute[Ohm][7];
		antifastattack_defence_refresh(bd);
	}
}

//拉里罗伯茨
void build_Larry_Roberts(int n){
	for (int i=0;;i++){
		if ( Message.Road[n].own_defence >= Message.Road[n].criticalpoint ) return;
		if ( Message.turnresource_count < OriginalBuildingAttribute[Larry_Roberts][6] ||
			Message.turnbuildingpoint_count < OriginalBuildingAttribute[Larry_Roberts][7] ) return;
		if ( Message.building_count >= 41 + 20 * state->age[ts19_flag] ) {selllist_for_defence();return;}
		Position s;
		for (int t=0;t<Larry_Roberts_list[n].size();t++){
			if ( able_to_build(Larry_Roberts_list[n][t]) ) {
				s=Larry_Roberts_list[n][t];break;}
		}
		if ( s.x == -1 ) 
			return;
		construct(Larry_Roberts,s);
		Building bd(Larry_Roberts,OriginalBuildingAttribute[Larry_Roberts][1],s,ts19_flag,0,0);
		Message.build_this_turn.push_back(bd.pos);
		Message.building_count++;
		Message.turnresource_count -= OriginalBuildingAttribute[Larry_Roberts][6];
		Message.turnbuildingpoint_count -= OriginalBuildingAttribute[Larry_Roberts][7];
		defence_refresh(bd);
	}
}
void build_Static_Larry(int n,int max){
	for (int i=0;i<max;i++){
		if ( Message.Road[n].Static_Larry >= max ) return;
		if ( Message.turnresource_count < OriginalBuildingAttribute[Larry_Roberts][6] ||
			Message.turnbuildingpoint_count < OriginalBuildingAttribute[Larry_Roberts][7] ) return;
		if ( Message.building_count >= 41 + 20 * state->age[ts19_flag] ) {selllist_for_defence();return;}
		Position s;
		for (int t=0;t<Larry_Roberts_list[n].size();t++){
			if ( able_to_build(Larry_Roberts_list[n][t]) ) {
				s=Larry_Roberts_list[n][t];break;}
		}
		if ( s.x == -1 ) 
			return;
		construct(Larry_Roberts,s);
		Building bd(Larry_Roberts,OriginalBuildingAttribute[Larry_Roberts][1],s,ts19_flag,0,0);
		Message.build_this_turn.push_back(bd.pos);
		Message.building_count++;
		Message.turnresource_count -= OriginalBuildingAttribute[Larry_Roberts][6];
		Message.turnbuildingpoint_count -= OriginalBuildingAttribute[Larry_Roberts][7];
		Message.Road[n].Static_Larry++;
	}
}
void upgrade_for_Larry(int n)
{
	for (int i=0;i<state->building[ts19_flag].size();i++){
		if ( Message.Road[n].own_defence >= Message.Road[n].criticalpoint ) return;
		if ( Message.turnresource_count < 0.5 * OriginalBuildingAttribute[Larry_Roberts][6] ||
			Message.turnbuildingpoint_count < 0.5 * OriginalBuildingAttribute[Larry_Roberts][7]) return;
		else if ( state->building[ts19_flag][i].building_type == Larry_Roberts && state->building[ts19_flag][i].level < state->age[ts19_flag] &&
			Larry_Roberts_point[n][state->building[ts19_flag][i].pos.x][state->building[ts19_flag][i].pos.y] ) {
				upgrade(state->building[ts19_flag][i].unit_id);
				Message.turnresource_count -= 0.5 * OriginalBuildingAttribute[Larry_Roberts][6];
				Message.turnbuildingpoint_count -= 0.5 * OriginalBuildingAttribute[Larry_Roberts][7];
				defence_refresh_update(state->building[ts19_flag][i]);}
	}
}
//马斯克（注：实测很难建起来，不过无伤大雅了）
void build_Musk(){
	for (int n=1;n<=road_count;n++){
		if ( Message.Road[n].enemy_soldier[7] ){
			if ( road_count == 7 && ( n == 1 || n == 7 ) ){
				bool build=0;
				if (!ts19_flag){
					for (int x=0;x<=105;x++){
						if ( dist(road_block[n][105],Position(x,105-x)) < 3 && able_to_build(Position(x,105-x)) ) {
							construct(Musk,Position(x,105-x));build=1;break;}
					}
					if (!build) selllist_for_Musk(n);
				}
				else {
					for (int x=0;x<=105;x++){
						if ( dist(road_block[n][105],Position(199-x,94+x)) < 3 && able_to_build(Position(199-x,94+x)) ) {
							construct(Musk,Position(199-x,94+x));build=1;break;}
					}
					if (!build) selllist_for_Musk(n);
				}
			}
			else{
				bool build=0;
				if (!ts19_flag){
					for (int x=0;x<=115;x++){
						if ( dist(road_block[n][115],Position(x,115-x)) < 3 && able_to_build(Position(x,115-x)) ) {
							construct(Musk,Position(x,115-x));build=1;break;}
					}
					if (!build) selllist_for_Musk(n);
				}
				else {
					for (int x=0;x<=115;x++){
						if ( dist(road_block[n][115],Position(199-x,84+x)) < 3 && able_to_build(Position(199-x,84+x)) ) {
							construct(Musk,Position(199-x,84+x));build=1;break;}
					}
					if (!build) selllist_for_Musk(n);
				}
			}
		}
	}
}
//霍金
void build_Hawkin(int n,int max){
	for (int i=0;;i++){
		if ( Message.Road[n].Hawkincount >= max ) return;
		if ( Message.turnresource_count < OriginalBuildingAttribute[Hawkin][6] ||
			Message.turnbuildingpoint_count < OriginalBuildingAttribute[Hawkin][7] ) return;
		if ( Message.building_count >= 41 + 20 * state->age[ts19_flag] ) {selllist_for_defence();return;}
		Position s;
		for (int t=0;t<Hawkin_list[n].size();t++){
			if ( able_to_build(Hawkin_list[n][t]) ) {
				s=Hawkin_list[n][t];break;}
		}
		if ( s.x == -1 ) 
			return;
		construct(Hawkin,s);
		Building bd(Hawkin,OriginalBuildingAttribute[Hawkin][1],s,ts19_flag,0,0);
		Message.build_this_turn.push_back(bd.pos);
		Message.building_count++;
		Message.turnresource_count -= OriginalBuildingAttribute[Hawkin][6];
		Message.turnbuildingpoint_count -= OriginalBuildingAttribute[Hawkin][7];
		defence_refresh(bd);
	}
}
int homeclear(){
	for (int x=8;x<15;x++){
		for (int y=8;y<15;y++){
			if ( able_to_build(Position(x,y)) ) {
				construct(Hawkin,Position(x,y));
				return 0;}
		}
	}
	return -1;
}

//——————————统一指令——————————

//修建码农（艺术风格的来源）
void build_Programmer(Position p){
	if ( Message.turnresource_count <  OriginalBuildingAttribute[17][6] ||
		Message.turnbuildingpoint_count < OriginalBuildingAttribute[17][7] ||
		Message.building_count >= 41 + 20 * state->age[ts19_flag] ||
		Message.placed.size() > 80 + 5 * (road_count/2) )	return;
	for (int i=0;i<Message.placed.size();i++){
		if ( p.x==Message.placed[i].x && p.y==Message.placed[i].y ) return;}
	if ( able_to_build(p) ) {
		construct(Programmer,p);
		Message.build_this_turn.push_back(p);Message.building_count++;
		Message.placed.push_back(p);
		Message.turnresource_count -= OriginalBuildingAttribute[17][6];
		Message.turnbuildingpoint_count -= OriginalBuildingAttribute[17][7];}
	else if ( able_to_build( Position(p.x-1,p.y) )) {
		construct(Programmer,Position(p.x-1,p.y));
		Message.build_this_turn.push_back(Position(p.x-1,p.y));Message.building_count++;
		Message.placed.push_back(p);
		Message.turnresource_count -= OriginalBuildingAttribute[17][6];
		Message.turnbuildingpoint_count -= OriginalBuildingAttribute[17][7];}
	else if ( able_to_build( Position(p.x+1,p.y) )) {
		construct(Programmer,Position(p.x+1,p.y));
		Message.build_this_turn.push_back(Position(p.x+1,p.y));Message.building_count++;
		Message.placed.push_back(p);
		Message.turnresource_count -= OriginalBuildingAttribute[17][6];
		Message.turnbuildingpoint_count -= OriginalBuildingAttribute[17][7];}
	else if ( able_to_build( Position(p.x,p.y-1) )) {
		construct(Programmer,Position(p.x,p.y-1));
		Message.build_this_turn.push_back(Position(p.x,p.y-1));Message.building_count++;
		Message.placed.push_back(p);
		Message.turnresource_count -= OriginalBuildingAttribute[17][6];
		Message.turnbuildingpoint_count -= OriginalBuildingAttribute[17][7];}
	else if ( able_to_build( Position(p.x,p.y+1) )) {
		construct(Programmer,Position(p.x,p.y+1));
		Message.build_this_turn.push_back(Position(p.x,p.y+1));Message.building_count++;
		Message.placed.push_back(p);
		Message.turnresource_count -= OriginalBuildingAttribute[17][6];
		Message.turnbuildingpoint_count -= OriginalBuildingAttribute[17][7];}
	else return;
	if ( !ts19_flag ){
		if ( !dist(p,Position(22,22)) || !dist(p,Position(37,21)) || !dist(p,Position(21,37)) || !dist(p,Position(45,5)) || !dist(p,Position(5,45)) ||
			!dist(p,Position(69,5)) || !dist(p,Position(5,69)) || !dist(p,Position(57,17)) || !dist(p,Position(17,57)) || !dist(p,Position(38,38)) ) {
				protectlist.push_back(p);}
	}
	else {
		if ( !dist(p,Position(177,177)) || !dist(p,Position(162,178)) || !dist(p,Position(178,162)) || !dist(p,Position(154,194)) || !dist(p,Position(194,154)) ||
			!dist(p,Position(130,194)) || !dist(p,Position(194,130)) || !dist(p,Position(142,182)) || !dist(p,Position(182,142)) || !dist(p,Position(161,161)) ) {
				protectlist.push_back(p);}
	}
}
//空格子
void sellbool(){
	if ( Message.sellup ) return;
	if (!ts19_flag) {
		for (int i=0;i<state->building[ts19_flag].size();i++){
			if ( state->building[ts19_flag][i].building_type == Bool ){
				bool f=1;
				for (int j=0;j<Message.selllist.size();j++){
					if ( Message.selllist[j].unit_id == state->building[ts19_flag][i].unit_id ) {
						f=0;break;}
				}
				if (f) {
					sell(state->building[ts19_flag][i].unit_id);
					Message.selllist.push_back(state->building[ts19_flag][i]);
					return;}
			}
		}
	}
	else {
		for (int i=0;i<state->building[ts19_flag].size();i++){
			if ( state->building[ts19_flag][i].building_type == Bool ){
				bool f=1;
				for (int j=0;j<Message.selllist.size();j++){
					if ( Message.selllist[j].unit_id == state->building[ts19_flag][i].unit_id ) {
						f=0;break;}
				}
				if (f) {
					sell(state->building[ts19_flag][i].unit_id);
					Message.selllist.push_back(state->building[ts19_flag][i]);
					return;}
			}
		}
	}
}
void sellup_camp(){
	int count=0;
	for (int i=0;i<state->building[ts19_flag].size()-1;i++) {
		if ( state->building[ts19_flag][i].building_type <= 8 ) {
			sell(state->building[ts19_flag][i].unit_id);
			Message.selllist.push_back(state->building[ts19_flag][i]);
			count++;
			if ( count >= 20 ) break;
		}
	}
}
void selllist_for_Von(int n){
	if ( Message.sellup ) return;
	for (int i=0;i<state->building[ts19_flag].size();i++) {
		if ( state->building[ts19_flag][i].building_type == Programmer && camp_map_Von[n][state->building[ts19_flag][i].pos.x][state->building[ts19_flag][i].pos.y] ) {
			bool f=1;
			for (int j=0;j<Message.selllist.size();j++) {
				if ( Message.selllist[j].unit_id == state->building[ts19_flag][i].unit_id ) {
					f=0;break;}
			}
			if (f) {
				sell(state->building[ts19_flag][i].unit_id);
				Message.selllist.push_back(state->building[ts19_flag][i]);
				return;}
		}
	}
	if ( Message.building_count >= 41 + 20 * state->age[ts19_flag] ) {
		selllist_for_defence();return;}
}
void selllist_for_VonAdd(int n){
	if ( Message.sellup ) return;
	for (int i=0;i<state->building[ts19_flag].size();i++) {
		if ( state->building[ts19_flag][i].building_type == Programmer && camp_map_VonAdd[n][state->building[ts19_flag][i].pos.x][state->building[ts19_flag][i].pos.y] ) {
			bool f=1;
			for (int j=0;j<Message.selllist.size();j++) {
				if ( Message.selllist[j].unit_id == state->building[ts19_flag][i].unit_id ) {
					f=0;break;}
			}
			if (f) {
				sell(state->building[ts19_flag][i].unit_id);
				Message.selllist.push_back(state->building[ts19_flag][i]);
				return;}
		}
	}
	if ( Message.building_count >= 41 + 20 * state->age[ts19_flag] ) {
		selllist_for_defence();return;}
}
void selllist_for_NortonTony(int n){
	if ( Message.sellup ) return;
	for (int i=0;i<state->building[ts19_flag].size();i++) {
		if ( state->building[ts19_flag][i].building_type == Programmer && camp_map_NortonTony[n][state->building[ts19_flag][i].pos.x][state->building[ts19_flag][i].pos.y] ) {
			bool f=1;
			for (int j=0;j<Message.selllist.size();j++) {
				if ( Message.selllist[j].unit_id == state->building[ts19_flag][i].unit_id ) {
					f=0;break;}
			}
			if (f) {
				sell(state->building[ts19_flag][i].unit_id);
				Message.selllist.push_back(state->building[ts19_flag][i]);
				return;}
		}
	}
	if ( Message.building_count >= 41 + 20 * state->age[ts19_flag] ) {
		selllist_for_defence();return;}
}
void selllist_for_TheveninKao(int n){
	if ( Message.sellup ) return;
	for (int i=0;i<state->building[ts19_flag].size();i++) {
		if ( state->building[ts19_flag][i].building_type == Programmer && camp_map_TheveninKao[n][state->building[ts19_flag][i].pos.x][state->building[ts19_flag][i].pos.y] ) {
			bool f=1;
			for (int j=0;j<Message.selllist.size();j++) {
				if ( Message.selllist[j].unit_id == state->building[ts19_flag][i].unit_id ) {
					f=0;break;}
			}
			if (f) {
				sell(state->building[ts19_flag][i].unit_id);
				Message.selllist.push_back(state->building[ts19_flag][i]);
				return;}
		}
	}
	if ( Message.building_count >= 41 + 20 * state->age[ts19_flag] ) {
		selllist_for_defence();return;}
}
void selllist_for_Musk(int n){
	for (int i=0;i<state->building[ts19_flag].size();i++) {
		if ( road_count == 7 && ( n == 1 || n == 7 ) ) {
			if ( state->building[ts19_flag][i].building_type == Programmer && dist(road_block[n][110],state->building[ts19_flag][i].pos) < 6 ) {
				bool f=1;
				for (int j=0;j<Message.selllist.size();j++) {
					if ( Message.selllist[j].unit_id == state->building[ts19_flag][i].unit_id ) {
						f=0;break;}
				}
				if (f) {
					sell(state->building[ts19_flag][i].unit_id);
					Message.selllist.push_back(state->building[ts19_flag][i]);
					return;}
			}
		}
		else {
			if ( state->building[ts19_flag][i].building_type == Programmer && dist(road_block[n][120],state->building[ts19_flag][i].pos) < 6 ) {
				bool f=1;
				for (int j=0;j<Message.selllist.size();j++) {
					if ( Message.selllist[j].unit_id == state->building[ts19_flag][i].unit_id ) {
						f=0;break;}
				}
				if (f) {
					sell(state->building[ts19_flag][i].unit_id);
					Message.selllist.push_back(state->building[ts19_flag][i]);
					return;}
			}
		}
	}
	if ( Message.building_count >= 41 + 20 * state->age[ts19_flag] ) selllist_for_defence();
}
void selllist_for_defence(){
	if ( Message.sellup ) return;
	for (int i=0;i<state->building[ts19_flag].size();i++) {
		if ( (state->building[ts19_flag][i].building_type == Programmer &&
			dist(state->building[ts19_flag][state->building[ts19_flag].size()-1].pos,state->building[ts19_flag][i].pos) <= 90 ) ||
			state->building[ts19_flag][i].building_type == Bool || state->building[ts19_flag][i].building_type == Ohm  ) {
				bool f1=1;
				for (int j=0;j<protectlist.size();j++) {
					if ( dist ( state->building[ts19_flag][i].pos,protectlist[j] ) < 2 ) {
						f1=0;break;}
				}
				if (!f1) continue;
				bool f=1;
				for (int j=0;j<Message.selllist.size();j++) {
					if ( Message.selllist[j].unit_id == state->building[ts19_flag][i].unit_id ) {
						f=0;break;}
				}
				if (f) {
					sell(state->building[ts19_flag][i].unit_id);
					Message.selllist.push_back(state->building[ts19_flag][i]);
					return;}
		}
	}
	Message.sellup=1;
}
void antifastattack_selllist(){
	if (!ts19_flag) {
		for (int i=0;i<state->building[ts19_flag].size();i++) {
			if ( state->building[ts19_flag][i].building_type == Programmer && dist( Position(0,0),state->building[ts19_flag][i].pos ) < 48 ) {
				bool f=1;
				for (int j=0;j<Message.selllist.size();j++) {
					if ( Message.selllist[j].unit_id == state->building[ts19_flag][i].unit_id ) {
						f=0;break;}
				}
				if (f) {
					sell(state->building[ts19_flag][i].unit_id);
					Message.selllist.push_back(state->building[ts19_flag][i]);
					break;}
			}
		}
	}
	else {
		for (int i=0;i<state->building[ts19_flag].size();i++){
			if ( state->building[ts19_flag][i].building_type == Programmer && dist( Position(199,199),state->building[ts19_flag][i].pos ) < 48 ){
				bool f=1;
				for (int j=0;j<Message.selllist.size();j++){
					if ( Message.selllist[j].unit_id == state->building[ts19_flag][i].unit_id ) {
						f=0;break;}
				}
				if (f) {
					sell(state->building[ts19_flag][i].unit_id);Message.building_count--;
					Message.selllist.push_back(state->building[ts19_flag][i]);
					break;}
			}
		}
	}
}

//全体升级
void upgrade_for_all(BuildingType t){
	for (int i=0;i<state->building[ts19_flag].size();i++) {
		if ( Message.turnresource_count < 0.5 * OriginalBuildingAttribute[t][6] ||
			Message.turnbuildingpoint_count < 0.5 * OriginalBuildingAttribute[t][7]) return;
		else if ( state->building[ts19_flag][i].building_type == t && state->building[ts19_flag][i].level < state->age[ts19_flag] ){
			upgrade(state->building[ts19_flag][i].unit_id);
			Message.turnresource_count -= 0.5 * OriginalBuildingAttribute[state->building[ts19_flag][i].building_type][6];
			Message.turnbuildingpoint_count -= 0.5 * OriginalBuildingAttribute[state->building[ts19_flag][i].building_type][7];}
	}
}
//防御
void carry_defence(int n){
	if (!n) return;
	switch ( Message.Road[n].enemy_mode ) {
	case 1:
		upgrade_for_all(Hawkin);
		build_Hawkin(n,3);
		break;
	case 2:
		upgrade_for_Larry(n);
		build_Larry_Roberts(n);
		break;
	case 3:
		build_Hawkin(n,3);
		upgrade_for_all(Hawkin);
		upgrade_for_Larry(n);
		build_Larry_Roberts(n);
		build_Hawkin(n,5);
		break;
	}
}
void carry_antifastattack_defence(int n){
	if (!n) return;
	if ( Message.Road[n].Bitdefence < Message.Road[n].enemy_soldier[0] ) {
		if ( Message.defencemode < 0 ) {
			build_home_Bool(n);}
		else {
			build_line_Bool(n);}
	}
	if ( Message.Road[n].THNdefence < Message.Road[n].enemy_soldier[1] + Message.Road[n].enemy_soldier[2] ) {
		if ( Message.defencemode < 0 ) {
			build_home_Ohm(n);upgrade_for_all(Ohm);}
		else {
			build_line_Ohm(n);upgrade_for_all(Ohm);}
	}
}
//进攻
void carry_attack(){
	if ( Message.attackmode == 1 ) {
		build_Von_Neumann();build_Kuen_Kao(1,15);build_Tony_Stark(1,5);
		upgrade_for_all(Von_Neumann);upgrade_for_all(Kuen_Kao);upgrade_for_all(Tony_Stark);
		switch (road_count) {
		case 3://70
			build_Tony_Stark(2,3);build_Norton(2,3);
			build_Von_Neumann_Add();build_Kuen_Kao(3,15);build_Tony_Stark(3,5);
			break;
		case 5://60
			build_Kuen_Kao(1,25);build_Tony_Stark(1,8);
			build_Tony_Stark(2,3);build_Kuen_Kao(2,2);
			build_Norton(3,2);
			build_Norton(4,2);
			build_Norton(5,2);
			break;
		case 7://50
			build_Norton(2,1);
			build_Tony_Stark(3,3);build_Kuen_Kao(3,2);
			build_Norton(4,1);
			build_Tony_Stark(5,1);build_Kuen_Kao(5,2);
			build_Norton(6,1);
			build_Tony_Stark(7,1);build_Kuen_Kao(7,2);
			break;
		}
	}
	else if ( Message.attackmode == 2 ) {
		build_Von_Neumann();build_Kuen_Kao(1,15);build_Tony_Stark(1,5);
		upgrade_for_all(Von_Neumann);upgrade_for_all(Kuen_Kao);upgrade_for_all(Tony_Stark);
		switch (road_count) {
		case 3://90
			build_Kuen_Kao(1,25);
			build_Tony_Stark(2,3);build_Norton(2,3);
			build_Von_Neumann_Add();build_Kuen_Kao(3,25);build_Tony_Stark(3,5);
			break;
		case 5://80
			build_Kuen_Kao(1,25);build_Tony_Stark(1,8);
			build_Tony_Stark(2,3);build_Kuen_Kao(2,2);
			build_Von_Neumann_Add();build_Kuen_Kao(3,8);build_Tony_Stark(3,4);
			build_Norton(3,2);
			build_Norton(4,2);
			build_Norton(5,2);
			break;
		case 7://70
			build_Norton(2,1);
			build_Von_Neumann_Add();build_Kuen_Kao(3,12);build_Tony_Stark(1,5);
			build_Norton(4,1);
			build_Tony_Stark(5,1);build_Kuen_Kao(5,2);
			build_Norton(6,1);
			build_Tony_Stark(7,1);build_Kuen_Kao(7,2);
			break;
		}
	}
	else {
		sellup_camp();
		if (!ts19_flag) {
			for (int s=8;s<100;s+=2) {
				for (int x=0;x<s;x++) {
					if (Message.turnresource_count <  OriginalBuildingAttribute[17][6] ||
						Message.turnbuildingpoint_count < OriginalBuildingAttribute[17][7] ||
						Message.building_count >= 41 + 20 * state->age[ts19_flag] )	return;
					if (able_to_build(Position(x,s-x))) {
						construct(Programmer,Position(x,s-x));}
				}
			}
		}
		else {
			for (int s=390;s>298;s-=2) {
				for (int x=199;x>s-199;x--) {
					if (Message.turnresource_count <  OriginalBuildingAttribute[17][6] ||
						Message.turnbuildingpoint_count < OriginalBuildingAttribute[17][7] ||
						Message.building_count >= 41 + 20 * state->age[ts19_flag] )	return;
					if (able_to_build(Position(x,s-x))) {
						construct(Programmer,Position(x,s-x));}
				}
			}
		}
	}
}

//升级时代
void science(){
	if ( state->resource[ts19_flag].resource >= 2000 + 750 * state->age[ts19_flag] * state->age[ts19_flag] ) {
		updateAge();
		Message.turnresource_count -= 2000 + 750 * state->age[ts19_flag] * state->age[ts19_flag];}
}
//全体修理
void refresh_defence(){
	for (int i=0;i<state->building[ts19_flag].size();i++) {
		if ( state->building[ts19_flag][i].building_type < 9 ) continue;
		if ( Message.turnresource_count < 0.2 * OriginalBuildingAttribute[state->building[ts19_flag][i].building_type][6]
		* (1+0.5*state->building[ts19_flag][i].level))	return;

		if ( state->building[ts19_flag][i].heal < 0.8 * OriginalBuildingAttribute[state->building[ts19_flag][i].building_type][1]
		* (1+0.5*state->building[ts19_flag][i].level) ) {
			toggleMaintain(state->building[ts19_flag][i].unit_id);
			Message.turnresource_count -= 0.2 * OriginalBuildingAttribute[state->building[ts19_flag][i].building_type][6]
			* (1+0.5*state->building[ts19_flag][i].level);}
	}
}

void player0_age0(){
	switch (state->turn) {
	case 0:
		road_mark_map_set0();Message.defencemode=0;Message.sellup=0;break;
	case 1:case 2:case 3:case 4:case 5:case 6:case 7:
		if ( road_count == 7 ) {
			if ( state->turn == 1 ) {
				BoolOhm_home_point_set(state->turn);
				BoolOhm_line_point_set(state->turn);
				Hawkin_point_set1(1);
				Larry_Roberts_point_set1(1);}
			else if ( state->turn == 7 ) {
				BoolOhm_home_point_set(state->turn);
				BoolOhm_line_point_set(state->turn);
				Hawkin_point_set7(7);
				Larry_Roberts_point_set7(7);}
			else {
				BoolOhm_home_point_set(state->turn);
				BoolOhm_line_point_set(state->turn);
				Hawkin_point_set(state->turn);
				Larry_Roberts_point_set(state->turn);}
		}
		else {
			if ( state->turn <= road_count ) {
				BoolOhm_home_point_set(state->turn);
				BoolOhm_line_point_set(state->turn);
				Hawkin_point_set(state->turn);
				Larry_Roberts_point_set(state->turn);}
		}
		break;
	case 8:case 9:case 10:case 11:case 12:case 13:case 14:
		if ( state->turn-7 <= road_count ) {
			camp_map_TheveninKao_set0(state->turn-7);
			camp_map_ShaLee_set0(state->turn-7);
			camp_map_NortonTony_set0(state->turn-7);}
		break;
	case 15:
		camp_map_Von_set0();camp_map_VonAdd_set0();break;
	}

	if ( state->turn == 0 ) {
		build_Programmer(Position(10,10));build_Programmer(Position(14,14));build_Programmer(Position(18,18));
		build_Programmer(Position(22,22));build_Programmer(Position(26,26));build_Programmer(Position(30,30));}
	else {
		if ( Message.defencemode == -1 ) { 
			build_Shannon(1+road_count/7,3);build_Shannon(2+road_count/7,3);
			int s=58;
			for (int x=1;x<58;x+=4) {
				build_Programmer(Position(x,s-x));}
			s=50;
			for (int x=49;x>0;x-=4) {
				build_Programmer(Position(x,s-x));}
		}
		else if ( Message.defencemode == -2 ) {
			build_Shannon(road_count-road_count/7,3);build_Shannon(road_count-road_count/7-1,3);
			int s=58;
			for (int x=1;x<58;x+=4) {
				build_Programmer(Position(x,s-x));}
			s=50;
			for (int x=49;x>0;x-=4) {
				build_Programmer(Position(x,s-x));}
		}
		else {
			int s=58;
			for (int x=1;x<58;x+=4) {
				build_Programmer(Position(x,s-x));}
			s=50;
			for (int x=49;x>0;x-=4) {
				build_Programmer(Position(x,s-x));}

			build_Programmer(Position(1,65));build_Programmer(Position(65,1));
			build_Programmer(Position(5,69));build_Programmer(Position(69,5));
			build_Programmer(Position(9,73));build_Programmer(Position(73,9));
			build_Programmer(Position(34,34));build_Programmer(Position(38,38));
		}
	}
}
void player1_age0(){
	switch (state->turn) {
	case 0:road_mark_map_set1();Message.defencemode=0;Message.sellup=0;
		break;
	case 1:case 2:case 3:case 4:case 5:case 6:case 7:
		if ( road_count == 7 ) {
			if ( state->turn == 1 ) {
				BoolOhm_home_point_set(state->turn);
				BoolOhm_line_point_set(state->turn);
				Hawkin_point_set1(1);
				Larry_Roberts_point_set1(1);}
			else if ( state->turn == 7 ) {
				BoolOhm_home_point_set(state->turn);
				BoolOhm_line_point_set(state->turn);
				Hawkin_point_set7(7);
				Larry_Roberts_point_set7(7);}
			else {
				BoolOhm_home_point_set(state->turn);
				BoolOhm_line_point_set(state->turn);
				Hawkin_point_set(state->turn);
				Larry_Roberts_point_set(state->turn);}
		}
		else{
			if ( state->turn <= road_count ) {
				BoolOhm_home_point_set(state->turn);
				BoolOhm_line_point_set(state->turn);
				Hawkin_point_set(state->turn);
				Larry_Roberts_point_set(state->turn);}
		}
		break;
	case 8:case 9:case 10:case 11:case 12:case 13:case 14:
		if ( state->turn-7 <= road_count ) {
			camp_map_TheveninKao_set1(state->turn-7);
			camp_map_ShaLee_set1(state->turn-7);
			camp_map_NortonTony_set1(state->turn-7);}
		break;
	case 15:
		camp_map_Von_set1();camp_map_VonAdd_set1();break;
	}

	if ( state->turn == 0 ) {
		build_Programmer(Position(189,189));build_Programmer(Position(185,185));build_Programmer(Position(181,181));
		build_Programmer(Position(177,177));build_Programmer(Position(173,173));build_Programmer(Position(169,169));}
	else {
		if ( Message.defencemode == -1 ) {
			build_Shannon(1+road_count/7,3);build_Shannon(2+road_count/7,3);
			int s=340;
			for (int x=198;x>141;x-=4) {
				build_Programmer(Position(x,s-x));}
			s=348;
			for (int x=199;x>150;x-=4) {
				build_Programmer(Position(x,s-x));}
		}
		else if ( Message.defencemode == -2 ) {
			build_Shannon(road_count-road_count/7,3);build_Shannon(road_count-road_count/7-1,3);
			int s=340;
			for (int x=198;x>141;x-=4) {
				build_Programmer(Position(x,s-x));}
			s=348;
			for (int x=199;x>150;x-=4) {
				build_Programmer(Position(x,s-x));}
		}
		else {
			int s=340;
			for (int x=198;x>141;x-=4) {
				build_Programmer(Position(x,s-x));}
			s=348;
			for (int x=199;x>150;x-=4) {
				build_Programmer(Position(x,s-x));}

			build_Programmer(Position(198,134));build_Programmer(Position(134,198));
			build_Programmer(Position(194,130));build_Programmer(Position(130,194));
			build_Programmer(Position(190,126));build_Programmer(Position(126,190));
			build_Programmer(Position(165,165));build_Programmer(Position(161,161));
		}
	}
}
void player0_line1(){
	for (int x=65;x<90;x+=4) {
		int y=x-64;
		build_Programmer(Position(x,y));
	}
	build_Programmer(Position(93,21));
	for (int y=65;y<90;y+=4) {
		int x=y-64;
		build_Programmer(Position(x,y));
	}
	build_Programmer(Position(21,93));
}
void player0_line2(){	
	for (int x=38;x<62;x+=4) {
		int y=x;
		build_Programmer(Position(x,y));
	}
	for (int y=53;y<78;y+=4) {
		int x=y-40;
		build_Programmer(Position(x,y));
	}
	for (int x=53;x<78;x+=4) {
		int y=x-40;
		build_Programmer(Position(x,y));
	}
	for (int x=73;x<98;x+=8) {
		build_Programmer(Position(x,1));
	}
	for (int y=73;y<98;y+=8) {
		build_Programmer(Position(1,y));
	}
}
void player1_line1(){
	for (int x=134;x>109;x-=4) {
		int y=x+64;
		build_Programmer(Position(x,y));
	}
	build_Programmer(Position(106,178));
	for (int y=134;y>109;y-=4) {
		int x=y+64;
		build_Programmer(Position(x,y));
	}
	build_Programmer(Position(178,106));
}
void player1_line2(){
	for (int x=161;x>137;x-=4) {
		int y=x;
		build_Programmer(Position(x,y));
	}
	for (int y=146;y>121;y-=4) {
		int x=y+40;
		build_Programmer(Position(x,y));
	}
	for (int x=146;x>121;x-=4) {
		int y=x+40;
		build_Programmer(Position(x,y));
	}
	for (int x=126;x>101;x-=8) {
		build_Programmer(Position(x,198));
	}
	for (int y=126;y>101;y-=8) {
		build_Programmer(Position(198,y));
	}
}
void player0_boom(){
	for (int s=10;s<=78;s+=2) {
		for (int x=s/3;x>0;x-=2) {
			build_Programmer(Position(x,s-x));}
	}
}
void player1_boom(){
	for (int s=388;s>=320;s-=2) {
		for (int x=(199+s)/3;x<199;x+=2) {
			build_Programmer(Position(x,s-x));}
	}
}

void f_player(){
	start=clock();
	message_refresh();//在回合开始时刷新

	if ( state->age[ts19_flag] == 0 ) {
		science();
		if ( Message.defencemode ) {
			for (int n=0;n<=road_count;n++) {
				carry_antifastattack_defence( (state->turn+n) % (road_count+1) );}
		}

		if (!ts19_flag)	player0_age0();
		else	player1_age0();
	}
	else if ( state->age[ts19_flag] < 4 ) {
		science();
		refresh_defence();

		if ( Message.defencemode ) {
			for (int n=0;n<=road_count;n++) {
				carry_antifastattack_defence( (state->turn+n) % (road_count+1) );}
		}
		if ( Message.defencemode < 0 ) { 
			for (int n=1;n<=road_count;n++) {
				if ( Message.Road[n].enemy_soldier[0] + Message.Road[n].enemy_soldier[1] + Message.Road[n].enemy_soldier[2] ){
					build_Shannon(n,3*state->age[ts19_flag]);}
			}
		}

		if (!ts19_flag)	{
			player0_line1();
			player0_line2();
			player0_boom();
		}
		else {
			player1_line1();
			player1_line2();
			player1_boom();
		}

		upgrade_for_all(Programmer);
	}
	else if ( state->age[ts19_flag] == 4 ) {
		science();
		refresh_defence();
		if ( Message.defencemode < 0 ) {
			for (int n=1;n<=road_count;n++) {
				if ( Message.Road[n].enemy_soldier[0] + Message.Road[n].enemy_soldier[1] + Message.Road[n].enemy_soldier[2] ){
					build_Kuen_Kao(n,3);}
			}
		}
		else if ( Message.defencemode == 1 ) sellbool();

		for (int n=0;n<=road_count;n++) {
			carry_defence( (state->turn+n) % (road_count+1) );}

		upgrade_for_all(Programmer);
		build_Von_Neumann();
		build_Kuen_Kao(1,5);
		upgrade_for_all(Von_Neumann);
	}
	else {
		refresh_defence();
		if ( Message.defencemode < 0 ) {
			for (int n=1;n<=road_count;n++) {
				if ( Message.Road[n].enemy_soldier[0] + Message.Road[n].enemy_soldier[1] + Message.Road[n].enemy_soldier[2] ){
					build_Kuen_Kao(n,3);}
			}
			Message.defencemode=homeclear();
		}
		else if ( Message.defencemode == 1 ) sellbool();

		build_Musk();upgrade_for_all(Musk);
		for (int n=0;n<=road_count;n++) {
			carry_defence( (state->turn+n) % (road_count+1) );}


		upgrade_for_all(Programmer);
		carry_attack();
		switch ( road_count ) {
		case 3:
			build_Static_Larry(1,8);build_Static_Larry(3,8);upgrade_for_all(Larry_Roberts);break;
		case 5:
			build_Static_Larry(1,5);build_Static_Larry(5,5);upgrade_for_all(Larry_Roberts);break;
		case 7:
			build_Static_Larry(1,3);build_Static_Larry(7,3);upgrade_for_all(Larry_Roberts);break;
		}
	}

	finish=clock();duration=finish-start;
	cout<<"Turn:"<<state->turn<<'\t'<<"Delay: "<<duration<<endl;
}