// Word_Recognition.cpp : Defines the entry point for the console application.
//

#include "stdafx.h"
#include <iostream>
#include <fstream>
#include <string>
#include <math.h>
#include <conio.h>
#include <iomanip>
#include <vector>
#include <algorithm>

int const FrameSize = 320; //size of frame considered for calculation of ci's.
int const p=12;	//no. of cepstral coefficients.
int const MAX = 5000; //value to be normalized around.
int const N=5;	//Number of states
int const M=32;	//Number of obsevation symbols per state
int const T=85; //Time sequence length
int const MaxIterations = 20; //Number of times, the model is re-evaluted and adjusted.
long double const threshhold = 1e-30;   //Min threshold to be assigned to zero values in matrix B.

using namespace std;

//Global variables
int count_samples = 0;
int index_max;
int digit_count = 0;			//variable to store digits number, which is currently being tested.
int Num_Recordings = 20;	
double silenceSTE = 0;

//Globally defined arrays
vector<string> filenames;
string filenames_test[110];	//array to store all the testing files names.
long double initialInput[150000]; 
long double stable[7040];  //to store 85 overlapped frames values samples
long double hammingwin[FrameSize];
long double Ci[T][p];
long double Codebook[M][p];  //universal codebook.
int O[T];	//Observation sequence
int Q[T];	//state sequence.
long double tokhuraWg[p] = {1.0, 3.0, 7.0, 13.0, 19.0, 22.0, 25.0, 33.0, 42.0, 50.0, 56.0, 61.0}; 
long double rsw[p+1] = {1,2.552145064,3.998620616,5.240951087,6.194559037,6.794523159,6.999998098,6.796995188,6.1993348,5.247705452,4.006893748,2.561373731,1.009555917};
long double pstar;
long double Alpha[T][N];
long double Beta[T][N];
long double Gamma[T][N];
long double delta[T][N];
int Zai[T][N];
long double Sai[T-1][N][N];
//Model parameters A, B and Pi
long double A[N][N];
long double B[N][M];
long double Pi[N];
//temporary model parameters
long double Abar[N][N];
long double Bbar[N][M];
long double Pibar[N];
long double Atemp[N][N];
long double Btemp[N][M];
long double Pitemp[N];
long double prob_seq[100000];   //TO STORE PROBABLITY OF OBS_SEQ OF EACH WORD

//filestream input output objects
ifstream fin;
ofstream fout;

//FUNCTION TO READ THE CODEBOOK IN THE ARRAY.
void Read_CodebookValues()
{
	fin.open("codebook.txt"); //Read codebook file into matrix
	for(int n=0;n<M;n++)
	{
		for(int m=0;m<p;m++)
		{
			fin>>Codebook[n][m];
		}
	}
	fin.close();
}
//TO READ THE INPUT FROM FILE AND RECORDING THE NO. OF SAMPLES.
void takeInitialInput(string inputfile)
{
	long double a;
	int z=0;
	count_samples=0;

	fin.open(inputfile);
	if(fin != NULL)
	{
		while(fin>>a)
		{
			initialInput[z]=a;
			z++;
		}
		count_samples=z;
	}
	else
	{
		cout<<"file can't be opened.";
		exit(-1);
	}
	fin.close();
}
//FUNCTION TO PERFORM DC SHIFT OVER THE INPUT SAMPLES VALUES.
void getDC_NoiseValues(string inputfile)
{
	long double dc;	
	int count =0;
	fin.open(inputfile);

	if(fin != NULL)
	{
		long double x , amp = 0;
		while(fin)
		{
			fin >> x;
			amp = amp + x;	//sum of all the sample amplitudes , later will be used to find the mean ampitude(DC Shift) 
			count++;		// to count the total no. os samples considered.
		}
		dc = amp/count;	    //DC SHIFT VALUE.
	}
	else
	{
		cout<< "file can't be opened , or is empty.";
		exit(-1);
	}
	fin.close();
	//SUBSTRACT THE DC SHIFT VALUE FROM EACH SAMPLE 
	for(int i=0;i<count_samples;i++)
	{
		initialInput[i]=initialInput[i]-dc;
	}
}

//function to find the absolute maximum from the DC shifted input file.
long double find_max()
{
	long double a , max = 0;
	
	//loop to find the absolute maximum from the input file of samples.
	for(int i=0;i<count_samples;i++)			
	{
		a=initialInput[i];
		if(max < abs(a))
		{
			max = a;
			index_max = i;
		}
	}
	return max;
}

//function to normalize the DC shift corrected data.
void Normalize()
{
	long double a , max = 0;
	max = find_max();
	for(int i=0;i<count_samples;i++)
	{
		initialInput[i]=(initialInput[i]/max)*MAX;
	}	
}
//FUNCTION TO READ THE HAMMING WINDOW VALUES FROM FILE INTO ARRAY.
void getWindowValues()
{
	long double a;
	fin.open("windowFunction.txt");
	int i=0;
	if(fin != NULL)
	{
		while(fin && i < FrameSize)
		{
			fin >> a;
			hammingwin[i] = a;
			i++;
		}
	}
	fin.close();
}
//FUNCTION TO CALCULATE Ai,Ci BY DURBINS ALGORITHM.
void calculateAiCibyDurbin(long double R[],int index)
{
	ofstream fout;
	long double E[p+1];
	long double a[p+1][p+1];
	long double k[p+1];
	long double A[p+1];
	long double c[p+1];
	long double sum,sum1;

	E[0] = R[0];
	for(int i=1; i<= p; i++)
	{
		sum=0;
		for(int j=1;j<=i-1;j++)
		{
			sum = sum + a[j][i-1]*R[i-j];
		}
		if(i==1)
			sum=0;
		k[i] = (R[i] - sum)/E[i-1]; 
		a[i][i] = k[i];
		for(int j =1 ; j <=i-1; j++)
		{
			a[j][i] = a[j][i-1] - (k[i]*a[i-j][i-1]);
		}
		E[i] = (1-(k[i]*k[i]))*E[i-1];
	}
	for(int i=1;i<=p;i++)
	{
		A[i] = a[i][p];
	}

	//calculating Ci's.
	long double ln_2 = 0.693147180559945309417;
	c[0] = log(R[0]*R[0]) / ln_2;
	for(int m = 1 ; m < p +1 ; m++)
	{
		sum1 =0;
		for(int k = 1 ; k < m ; k++)
		{
			double ratio = (double)k/m;
			sum1 = sum1 + ratio*(c[k]*A[m-k]);
		}
		c[m] = A[m] + sum1;
	}
	for(int i=0;i<=p;i++)
	{
		c[i] = c[i]*rsw[i];
	}
	for(int i=0;i<p;i++)
	{
		Ci[index][i] = c[i+1];
	}
}
//FUNCTION TO FIND THE FRAMES AND APPLYING DURBINS OVER THE FRAMES
void takeInput_CalCi()
{
	int  z=0, k=0;

	//SELECTING 7040 SAMPLES OR 85 STABLE FRAMES
	if(index_max < 3520)
	{
		index_max = index_max + 1000;
		if(index_max < 3520)
			index_max =3520;
	}
	for(int i=(index_max-3520);i<=(index_max+3519);i++)
	{
		stable[z]=initialInput[i];
		z++;
	}
	//FOR 5 FRAMES CALCULATE Ri Ai Ci
	for(int i=0;i<T;i++)
	{
		k = i*80;
		long double samples[FrameSize];
		long double R[p+1];

		//READING 320 SAMPLES INTO AN ARRAY 
		for(int j=0;j<FrameSize;j++)
		{
			samples[j]=stable[k];
			k++;
		}
		//appying windowing on the 320 values of the current frame.
		for(int j=0; j<FrameSize; j++)
		{
			samples[j] = samples[j]*hammingwin[j]; 
		}
		//calculating Ri's.
		for(int k=0; k <= p ; k ++)
		{
			long double sum = 0;
			for(int m=0; m <= FrameSize - k -1 ; m++)
			{
				sum = sum + samples[m]*samples[m+k];
			}
			R[k] = sum;
			//cout<<R[k] <<"\t";
		}
		//Function call to calculate Ai & Ci.
		calculateAiCibyDurbin(R,i);
	}
}

//function to find distance between 2 vectors.
long double find_Distance(long double *x, long double *y)
{
	long double distance;
	long double  sum = 0;
	for(int i = 0 ; i < p ; i++)
	{
		long double d1=0.0,d2=0.0;
		d1 = *(x + i); 
		d2 = *(y + i);
		sum += tokhuraWg[i]*(d1 - d2)*(d1 - d2);
	}
	distance = sum;
	return distance;
}


//function to find minimum distance from all the distances with all codebook vectors.
int find_min(long double *arr)
{
	int index = 0;
	for(int i = 1; i < M ; i++)
	{
		if(arr[i] < arr[index])
			index = i;              
	}
	return index;
}
//FUNTION TO FIND THE OBSERVATION SEQUENCE VALUE FOR THE INPUT BASED ON EACH FRAME.
void Codebook_index()
{
	//RUN LOOP T TIMES FOR EACH OF t FRAME AND FIND DISTANCE WITH CODE BOOK VECTORS.
	for(int t=0;t<T;t++)
	{
		long double d[M];
		for(int r=0;r<M;r++)
		{
			d[r]=0.0;
		}
		for(int i=0;i<M;i++)
		{
			d[i] = find_Distance(Ci[t] , Codebook[i]);
		}
		//mapping to the index having lowest distance with the frame Ci's.
		int index = find_min(d);
		O[t]=index+1;
	}
}
//HMM Starts from here
//FUNCTION TO READ THE MODEL VALUES FROM FILE
void LoadInitialModel()
{
	ifstream inFile;
	int i=0,j=0;
	inFile.open("A_MATRIX.txt"); //Read Initial A matrix

	for(int m=0;m<N;m++)
	{
		for(int n=0;n<N;n++)
		{
			inFile>>A[m][n];
		}
	}
	inFile.close();

	inFile.open("B_MATRIX.txt"); //Read Initial B matrix
	for(int n=0;n<N;n++)
	{
		for(int m=0;m<M;m++)
		{
			inFile>>B[n][m];
		}
	}
	inFile.close();

	inFile.open("PI_MATRIX.txt"); //Read Initial PI matrix
	for(int n=0;n<N;n++)
	{
		inFile>>Pi[n];
	}
	inFile.close();
}

//loading updated average model.
void LoadUpdatedAveragedModel(long long int file_no)
{
	ifstream inFile;
	string fname = "Model_A_" + filenames[file_no] + "_" + to_string(file_no) +".txt";
	int i=0,j=0;
	inFile.open(fname); //Read Initial A matrix

	for(int m=0;m<N;m++)
	{
		for(int n=0;n<N;n++)
		{
			inFile>>A[m][n];
		}
	}
	inFile.close();
	string fnameB = "Model_B_" + filenames[file_no] + "_" + to_string(file_no) +".txt";
	inFile.open(fnameB); //Read Initial B matrix
	for(int n=0;n<N;n++)
	{
		for(int m=0;m<M;m++)
		{
			inFile>>B[n][m];
		}
	}
	inFile.close();
}

//Displaying the matrices of the model.
void DisplayModelValues(long double C[N][N], long double D[N][M], long double I[T])
{
	int i , j;
	cout << "\nState Transition Probabity distribution Matrix:\n";
	for(i=0;i<N;i++)
	{
		for(j=0;j<N;j++)
			cout <<setprecision(10)<< C[i][j] << "\t";
		cout << "\n";
	}
	cout << "Observation symbol probability distribution Matrix:\n";
	for(i=0;i<N;i++)
	{
		for(j=0;j<M;j++)
			cout <<setprecision(10)<< D[i][j] << "\t";
		cout << "\n";
	}
	cout << "Initial state distribution Matrix:\n";
	for(i=0;i<N;i++)
	{
		cout <<setprecision(10)<< I[i] <<"\t";
	}
	cout << "\n";
}
//Writing Model to the file.
void WriteModelValues(string fn)
{
	int i , j;
	ofstream fout;
	fout.open(fn);
	if(fout != NULL)
	{
		fout << "State Transition Probabity distribution Matrix:\n";
		for(i=0;i<N;i++)
		{
			for(j=0;j<N;j++)
				fout <<setprecision(10)<< A[i][j] << "\t";
			fout << "\n";
		}
		fout << "Observation symbol probability distribution Matrix:\n";
		for(i=0;i<N;i++)
		{
			for(j=0;j<M;j++)
				fout <<setprecision(10)<< B[i][j] << "\t";
			fout << "\n";
		}
		fout << "Initial state distribution Matrix:\n";
		for(i=0;i<N;i++)
		{
			fout <<setprecision(10)<< Pi[i] <<"\t";
		}
		fout << "\n";
	}
	else
	{
		cout<<"File can't be open.";
		exit(-1);
	}
	fout.close();
}

//loading newly adjusted model to the model A,B,Pi.
void LoadAdjustedModel(long double Abar[N][N], long double Bbar[N][M],long double Pibar[N])
{
	int i , j;
	for(i=0;i<N;i++)
	{
		for(j=0;j<N;j++)
		{
			A[i][j]= Abar[i][j];
		}
	}
	for(i=0;i<N;i++)
	{
		for(j=0;j<M;j++)
		{
			B[i][j]= Bbar[i][j];
		}
	}
	for(i=0;i<N;i++)
	{
		Pi[i]=Pibar[i];
	}
}

//Method to load the observation sequence from the file.
void LoadObservationSequence(string filename)
{
	fin.open(filename, ios::in); 
	int a =0;
	int i=0;
	if(fin != NULL)
	{
		while(i<T)
		{
			fin >> a;
			O[i] =a;
			i++;
		}
	}
	else
	{
		cout<<"file can't be opened.";
		exit(-1);
	}
	fin.close();
}

//Calculation of alpha variable to find the solution of problem number 1.
void ForwardProcedure()
{
	int i , j , t;
	long double sum , P_Obs_for_Model = 0;
	int index = O[0]-1;
	for(i=0;i<N;i++)
	{
		Alpha[0][i] = Pi[i]*B[i][index];
	}
	for(t=0;t<T-1;t++)
	{
		index = O[t+1]-1;
		for(i=0;i<N;i++)
		{
			sum = 0;
			for(j=0;j<N;j++)
			{
				sum = sum + Alpha[t][j]*A[j][i];
			}
			Alpha[t+1][i]=sum*B[i][index];
		}
	}
	for(i=0;i<N;i++)
	{
		P_Obs_for_Model = P_Obs_for_Model + Alpha[T-1][i];
	}
	prob_seq[digit_count]=P_Obs_for_Model;
	//cout << P_Obs_for_Model <<"\n";
}
//Calculation of Beta variable.
void BackwardProcedure()
{
	int i , j , t;
	long double sum;
	int index = 0;
	for(i=0;i<N;i++)
	{
		Beta[T-1][i] = 1;
	}
	for(t=T-2;t>=0;t--)
	{
		index = O[t+1]-1;
		for(i=0;i<N;i++)
		{
			sum = 0;
			for(j=0;j<N;j++)
			{
				sum = sum + B[j][index]*A[i][j]*Beta[t+1][j];
			}
			Beta[t][i]=sum;
		}
	}
}
//Calculation of gamma variable , which is goinf to be used in solution of problem no. 3.
void CalculateGamma()
{
	int i , j , t;
	long double sum;
	for(t=0;t<T;t++)
	{
		sum = 0;
		for(j=0;j<N;j++)
		{
			sum = sum + Alpha[t][j]*Beta[t][j];
		}
		for(i=0;i<N;i++)
		{
			Gamma[t][i]= Alpha[t][i]*Beta[t][i]/sum;
		}
	}
}

//Finding the state sequence for the provided observation sequence.
void ViterbiAlgo()
{
	int i , j , t ,max;
	//Initialization
	int index =  O[0]-1;
	long double Pnew;
	for(i=0;i<N;i++)
	{
		delta[0][i] = Pi[i]*B[i][index];
		Zai[0][i] = 0; 
	}
	//Induction step
	for(t=1;t<T;t++)
	{
		index = O[t]-1;
		for(j=0;j<N;j++)
		{
			max = 0;
			for(i=1;i<N;i++)
			{
				if(delta[t-1][i]*A[i][j] > delta[t-1][max]*A[max][j])
					max = i;
			}
			Zai[t][j]=max;
			delta[t][j]= delta[t-1][max]*A[max][j]*B[j][index];
		}
	}
	//termination
	max=0;
	for(i=1;i<N;i++)
	{
		if(delta[T-1][i]>delta[T-1][max])
			max=i;
	}
	pstar = delta[T-1][max];
	cout<< "\nProbabilty P*: " << pstar;
	//Path Back tracking
	Q[T-1] = max;
	for(t=T-2;t>=0;t--)
	{
		int nextindex;
		nextindex = Q[t+1];
		Q[t] = Zai[t+1][nextindex];
	}
}
//Calculting sai variable fro the solution of problem no. 3.
void CalculatingSai()  //Baum_Welch
{
	int i , j , t , index;
	long double sum = 0;
	
	for(t=0;t<T-1;t++)
	{
		index = O[t+1]-1;
		sum = 0;
		for(i=0;i<N;i++)
		{
			for(j=0;j<N;j++)
			{
				sum = sum + Alpha[t][i]*A[i][j]*B[j][index]*Beta[t+1][j];
			}
		}
		for(i=0;i<N;i++)
		{
			long double x;
			for(j=0;j<N;j++)
			{
				x = Alpha[t][i]*A[i][j]*B[j][index]*Beta[t+1][j];
				Sai[t][i][j]= x/sum;
			}
		}
	}
}
//Solution to probelm no. 3, i.e. re-evaluation of model.
void ReEvaluationModel()
{
	int i , j , k ,t;
	long double sum1=0 , sum2 =0;
	//Re-evaluating Pi
	for(i=0;i<N;i++)
	{
		Pibar[i] = Gamma[0][i];
	}
	//Re-evaluating A
	for(i=0;i<N;i++)
	{
		long double sum2=0;
		for(int t=0;t<T-1;t++)
		{
			sum2+=Gamma[t][i];
		}
		for(j=0;j<N;j++)
		{
			sum1 =0;
			for(t=0;t<T-1;t++)
			{
				sum1 = sum1 + Sai[t][i][j];				
			}
			Abar[i][j] = sum1/sum2;
		}
	}
	//Re-evaluating B
	for(j=0;j<N;j++)
	{
		int count=0;
		long double max=0;
		int index=0;
		for(k=0;k<M;k++)
		{
			sum1 =0 , sum2 =0;
			for(t=0;t<T;t++)
			{
				sum1 = sum1 + Gamma[t][j];
				if(O[t]==k+1)
				{
					sum2 = sum2 + Gamma[t][j];				
				}
			}
			Bbar[j][k] = sum2/sum1;
			if(Bbar[j][k]>max)
			{
				max=Bbar[j][k];
				index=k;
			}

			if(Bbar[j][k]<threshhold)
			{
				Bbar[j][k]=threshhold;
				count++;
			}
		}
		Bbar[j][index]=max-count*threshhold;
	}
	LoadAdjustedModel(Abar, Bbar , Pibar);
	//DisplayModelValues(Abar, Bbar , Pibar);
}
//Enhancement of obtained model starts here

//function to initialize temporary model to 0 for each iteration of averaging.
void initializeTempModel()
{
	int i , j;
	for(i=0;i<N;i++)
	{
		for(j=0;j<N;j++)
		{
			Atemp[i][j] =0;
		}
	}
	for(i=0;i<N;i++)
	{
		for(j=0;j<M;j++)
		{
			Btemp[i][j] =0;
		}
	}
	for(i=0;i<N;i++)
	{
		Pitemp[i] =0;
	}
}

//FUNTION TO AVERAGE THE MODEL AFTER COUNT ITERATIONS.
void AvarageModels(long long int digit_no)
{
	string f1 = "Model_A_" + filenames[digit_no] + "_" + to_string(digit_no) +".txt";
	int i , j;

	fout.open(f1);
	if(fout != NULL)
	{
		for(i=0;i<N;i++)
		{
			for(j=0;j<N;j++)
			{
				Atemp[i][j] /= 20;
				cout<<Atemp[i][j];
				fout <<setprecision(10)<< Atemp[i][j] << "\t";
			}
			fout << "\n";
		}
	}
	else
	{
		cout<<"File can't be open.";
		exit(-1);
	}
	fout.close();
	string f2 = "Model_B_"+ filenames[digit_no] + "_" + to_string(digit_no) +".txt";
	fout.open(f2);
	if(fout != NULL)
	{
		for(i=0;i<N;i++)
		{
			for(j=0;j<M;j++)
			{
				Btemp[i][j] /= 20;
				cout<<Btemp[i][j];	
				fout <<setprecision(10)<< Btemp[i][j] << "\t";
			}
			fout << "\n";
		}
		fout << "Initial state distribution Matrix:\n";
	}
	else
	{
		cout<<"File can't be open.";
		exit(-1);
	}
	fout.close();

	string f3 = "Model_Pi_"+ filenames[digit_no] + "_" + to_string(digit_no) +".txt";
	fout.open(f3);
	if(fout != NULL)
	{
		for(i=0;i<N;i++)
		{
			Pitemp[i]/=20;
			fout <<setprecision(10)<< Pitemp[i] <<"\t";
		}
		fout << "\n";
	}
	else
	{
		cout<<"File can't be open.";
		exit(-1);
	}
	fout.close();
}

//fundtion to take all the trained models and predicting the probability of generation test observation with these models.
void testing()
{
	int accuracy =0;
	//keeping all the testing files in the array.
	//string location = "C:\\Users\\Vandana\\Documents\\Visual Studio 2010\\Projects\\DigitRecognition_HMM\\DigitRecognition_HMM\\194101055_digit\\";
	string filename;
	//LOOP FOR 10 DIGITS
	for(int y=0;y<filenames.size();y++)
	{
		cout<<endl<<"DIGIT : "<<y<<endl;
		//Initialization of filenames array to contain all the files to be tested in loop.

		//LOOP FOR 10 FILES OF EACH DIGIT
		for(int q=0;q<10;q++)
		{
			digit_count=0;
			//filename = location + filenames_test[index_file + q];
			long long int pos = q+21;
			filename = filenames[y] + "_" + to_string(pos) + ".txt";
			//cout<<filename<<endl;
			takeInitialInput(filename);
			getDC_NoiseValues("silence.txt");
			Normalize();
			takeInput_CalCi();
			Codebook_index();

			//TO CALCULATE PROBABILITY WITH EACH DIGIT
			for(int u=0;u<filenames.size();u++)
			{
				int i=0,j=0;
				long long int s=u;
				long double data;
				string filename;
				string filename2;
				filename="Model_A_" + filenames[s] + "_" + to_string(s) +".txt";
				filename2="Model_B_" + filenames[s] + "_" + to_string(s) +".txt";
				fin.open(filename);
				for(int m=0;m<N;m++)
				{
					for(int n=0;n<N;n++)
					{
						fin>>A[m][n];
					}
				}
				fin.close();
				fin.open(filename2); //Read Initial B matrix
				for(int n=0;n<N;n++)
				{
					for(int m=0;m<M;m++)
					{
						fin>>B[n][m];
					}
				}
				fin.close();
				ForwardProcedure();
				digit_count++;
			}

			//TO FIND MAX PROBABILITY
			long double max_value=0;
			int max_index=0;
			for(int d=0;d<filenames.size();d++)
			{
				//cout<<"prob"<<d<<"  "<<prob_seq[d]<<endl;
				if(prob_seq[d]>max_value)
				{
					max_value=prob_seq[d];
					max_index=d;
				}
			}
			//TO CALCULATE ACCURACY
			if(max_index==y)
				accuracy++;
			cout<<"Digit is : "<<filenames[max_index]<<endl;
		}
	}
	cout<<endl<<"ACCURACY IS : "<<accuracy<<endl;
}

double STE_Calculation_disjointWindow(){
	vector<double> ste;
	int offset = count_samples%320;
	int Size = count_samples - offset;
	double STE;
	for(int i=0;i<Size;i += 320){
		STE = 0;
		for(int j = i;j<320 + i;j++){
			STE = STE + (initialInput[j]*initialInput[j]);
		}
		double res = STE / 320;
		ste.push_back(res);
	}
	double avgSTE;
	double sum = 0;
	for(int i = 0;i<ste.size();i++){
		sum = sum + ste[i];
	}
	avgSTE = sum/ste.size();
	return avgSTE;
}

//fundtion to take all the trained models and predicting the probability of generation test observation with these models.
void Live_testing()
{
	cout<< "Record the word for testing.\n";
	while(1)
	{
		digit_count=0;
		//INITIALIZING THE PROBABILITY ARRAY FOR EACH OF THE RECORDED INPUT.
		for(int i = 0 ; i <filenames.size() ; i++)
			prob_seq[i] = 0;
		string filename;
		filename = "live_Refinput.txt";
		system("Recording_Module.exe 3 live_Refinput.wav live_Refinput.txt");
		takeInitialInput(filename);
		double avgSTE = STE_Calculation_disjointWindow();
		if(silenceSTE + 100 > avgSTE){
			cout<<"you haven't spoke any word"<<endl;
			return;
		}
		getDC_NoiseValues("silence.txt");
		Normalize();
		takeInput_CalCi();
		Codebook_index();
		//TO CALCULATE PROBABILITY WITH EACH WORD
		for(int u=0;u<filenames.size();u++)
		{
			int i=0,j=0;
			long long int s=u;
			long double data;
			string filename;
			string filename2;
			filename="Model_A_" + filenames[s] + "_" + to_string(s) +".txt";
			filename2="Model_B_" + filenames[s] + "_" + to_string(s) +".txt";
			fin.open(filename);
			for(int m=0;m<N;m++)
			{
				for(int n=0;n<N;n++)
				{
					fin>>A[m][n];
				}
			}
			fin.close();
			fin.open(filename2); //Read Initial B matrix
			for(int n=0;n<N;n++)
			{
				for(int m=0;m<M;m++)
				{
					fin>>B[n][m];
				}
			}
			fin.close();
			ForwardProcedure();
			digit_count++;
		}

		//TO FIND MAX PROBABILITY
		long double max_value=0;
		int max_index=0;
		for(int d=0;d<filenames.size();d++)
		{
			//cout<<"prob"<<d<<"  "<<prob_seq[d]<<endl;
			if(prob_seq[d]>max_value)
			{
				max_value=prob_seq[d];
				max_index=d;
			}
		}
		//TO CALCULATE ACCURACY
		cout<<"Word is : "<<filenames[max_index]<<endl;
		B:cout<<"Want to test another word (y/n) : ";
		char c;
		cin>>c;
		if(c == 'y' || c == 'Y'){
			continue;
		}else if(c == 'n' || c == 'N'){
			break;
		}else{
			cout<<"invalid input"<<endl;
			goto B;
		}
	}
}

void Training(long long int d){
	string filename;
	for(long long int avloop=0;avloop<3;avloop++){
		long long int f;
		initializeTempModel();
		for(f=0;f<Num_Recordings;f++)
		{
			long long i = 1;
			//filename = location + filenames[index_file + f];
			filename = "live_Refinput_" + to_string(f+1) + ".txt";
			takeInitialInput(filename);
			getDC_NoiseValues("silence.txt");
			Normalize();
			//take the input from the steady part of speech and calculate Ci's for the frame.
			takeInput_CalCi();     
			Codebook_index();
			if(avloop == 0)
				LoadInitialModel();
			else					
				LoadUpdatedAveragedModel(d);
			for(i=1;i<=MaxIterations;i++)
			{
				//Solution to problem no. 1
				ForwardProcedure();
				BackwardProcedure();
				CalculateGamma();
				//Solution to problem 2 is Viterbi Algorithm
				ViterbiAlgo();
				CalculatingSai();
				//Solution to problem no. 3
				ReEvaluationModel();
			}
			for(int r=0;r<N;r++)
			{
				for(int t=0;t<N;t++)
				{
					Atemp[r][t]=Atemp[r][t]+A[r][t];
				}
			}

			for(int r=0;r<N;r++)
			{
				for(int t=0;t<M;t++)
				{
					Btemp[r][t]=Btemp[r][t]+B[r][t];
				}
			}
			for(int r=0;r<N;r++)
			{
				Pitemp[r]=Pitemp[r]+Pi[r];
			}
		}
		AvarageModels(d);
	}
}

void Read_Trained_words(){
	fin.open("Trained_Words.txt");
	if(fin.is_open()){
		//reading words from the vector filenames
		string x;
		while(fin >> x){
			filenames.push_back(x);
		}
		fin.close();
	}else{
		cout<<" file is not open"<<endl;
	}
}

void AddWord(){
	fout.open("Trained_Words.txt");
	if(fout.is_open()){
		//storing words into the vector filenames
		for(int i=0;i<filenames.size();i++){
			fout<<filenames[i]<<endl;
		}
		fout.close();
	}else{
		cout<<" file is not open"<<endl;
	}
}

void Live_Training_data(){
	cout<<"you have been given 3 sec to record each utterances of the word"<<endl;
	cout<<"record 20 times"<<endl;
	cout<<"press any key to start recording"<<endl;
	getch();
	for(long long int i = 1;i<=Num_Recordings;i++){
		cout<<i<<" : "<<endl;
		string filename;
		filename = "live_Refinput_"+to_string(i)+".txt";
		system("Recording_Module.exe 3 live_Refinput.wav live_Refinput.txt");	
		char old_name[] = "live_Refinput.txt";
		char new_name[50];
		for(int j = 0;j<filename.length();j++){
			new_name[j] = filename[j];
		}
		new_name[filename.size()] = '\0';
		int val = rename("live_Refinput.txt", new_name);
	}
}

void DeleteFiles(){
	for(long long int i = 1;i<=Num_Recordings;i++){
		string filename;
		filename = "live_Refinput_"+to_string(i)+".txt";
		char new_name[50];
		for(int j = 0;j<filename.length();j++){
			new_name[j] = filename[j];
		}
		new_name[filename.size()] = '\0';
		remove(new_name);
	}
}

int _tmain(int argc, _TCHAR* argv[])
{
	Pi[0]=1;
	for(int j=1;j<N;j++)
	{
		Pi[j]=0;
	}
	Read_Trained_words();
	cout<<"words that are already trained shown below"<<endl;
	if(filenames.size() == 0){
		cout<<"there are no trained words"<<endl;
	}else{
		for(int i = 0;i<filenames.size();i++){
			cout<<filenames[i]<<endl;
		}
		cout<<endl;
	}
	//reading codebook;
	Read_CodebookValues();
	getWindowValues();
	cout<<"press any key and wait for 3 seconds, dont speak anything we are collecting silence or surrounding noise"<<endl;
	getch();
	system("Recording_Module.exe 3 silence.wav silence.txt");
	takeInitialInput("silence.txt");
	silenceSTE = STE_Calculation_disjointWindow();
	A:cout<<endl<<"=================================================================="<<endl;
	cout<<"press 1 for live training of new word"<<endl;
	cout<<"press 2 for live testing"<<endl;
	cout<<"press 3 for exit"<<endl;
	int choice;
	cout<<"enter choice : ";
	cin>>choice;
	if(choice == 1){
		string word;
		cout<<"enter the word which you want to train : ";
		cin>>word;
		transform(word.begin(), word.end(), word.begin(), ::tolower);
		int index = -1;
		for(int i = 0;i<filenames.size();i++){
			if(filenames[i] == word){
				index = i;
				break;
			}
		}
		if(index > -1){
			cout<<"word is already exist"<<endl;
		}else{
			filenames.push_back(word);
			Live_Training_data();
			Training(filenames.size()-1);
			DeleteFiles();
			AddWord();
		}
		goto A;
	}else if(choice == 2){
		Live_testing();
		goto A;
	}else if(choice == 3){
		cout<<"exited"<<endl;
	}else{
		cout<<"wrong choice enter again"<<endl;
		goto A;
	}

	//testing();
	return 0;
}