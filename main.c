// Timing C/ASM Mix Example
//Modified by Nestor Arteaga and Jocsan Cano
// Jason Losh

//-----------------------------------------------------------------------------
// Hardware Target
//-----------------------------------------------------------------------------

// Target Platform: EK-TM4C123GXL Evaluation Board
// Target uC:       TM4C123GH6PM
// System Clock:    40 MHz

// Hardware configuration:
// Green LED:


//-----------------------------------------------------------------------------
// Device includes, defines, and assembler directives
//-----------------------------------------------------------------------------
//Linearization formula y = - 0.0002x + 0.5328
//2nd linearization adapted and calibrated from new data y = -0.00025x + 0.5323
//example of algorithm  - 1-take the limit to were clipping needs to be. i.e take mVolts on this example imagine setting clipping to 400 mV
//step 2 -  convert mVolts to decimals. Divide by 1000.0 the units will become 0.40
//step 3 - find lower limit DAC unit by setting "Y" = 0.40 and solve linearization for "X".
//step 4 - find upper limit DAC unit by setting "Y" = -0.40 and solve linearization for "X"
//step 5 - read DAC unit from array if DAC unit Greater than or equal to LowerLimitX and lower than UpperLimitX, then Write to DAC
//Notes to implement, taking mV to clip and finding limits needs to happen before entering the ISR.




#include <inttypes.h>
#include <stdio.h>
#include <float.h>
#include <math.h>
#include <clock.h>
#include "wait.h"
#include <stdint.h>
#include <stdbool.h>
#include <stdlib.h>
#include "gpio.h"
#include "uart0.h"
#include "spi0.h"
#include "nvic.h"
#include <stdbool.h>
#include "tm4c123gh6pm.h"
#include <time.h>

#define SCLK PORTA,2
#define FSS PORTA,3
#define TX PORTA,5
#define LDAC PORTA,7
#define MAX_CHARS 80
#define MAX_FIELDS 5
#define ALPHA(c) (((c) >= 'a' && (c) <= 'z') || ((c) >= 'A' && (c) <= 'Z'))
#define IS_NUM(c) (((c) >= '0' && (c) <= '9') || (c) == '-' || (c) == '.')
#define PI 3.14159265
#define LUT_SIZE 4096
#define CS PORTA,3              //NEEDED?
#define GAIN_I 1944     //Channel A change value?
#define GAIN_Q 1944     //Channel B
#define EIGTH_QAM_GAIN 1360
#define H_GAIN 1360
#define H_16QAM_GAIN 680
#define DAC_B 0xB000
#define DAC_A 0x3000




//GLOBAL VARIABLES
float m_Slope = -0.00028;
float b_Intercept = 0.5323;
float clipToAmplitude;
uint16_t clipLowerLimit;
uint16_t clipUpperLimit;

uint16_t star = 0;
uint8_t bytes = 0;
uint16_t starval = 0;
uint32_t fs = 100000;   //sample rate
uint32_t deltaPhase = 0;
uint32_t phaseAccumulator_A = 0;
uint32_t phaseAccumulator_B = 0;
uint16_t deltaPhase_A = 0;
uint16_t deltaPhase_B = 0;
uint32_t phi_Index = 0;
uint32_t frequency = 10000;
float sinVal;
bool    dummy = false;
bool    sineChannelB = false;
bool    sineChannelA = false;
bool    bpskf = false;
bool    qpskf = false;
bool    eightpskf = false;
bool    qamf = false;
bool    RRC = false;
bool    clipping = false;

//LUT
uint16_t sineLut[LUT_SIZE];

uint8_t random[30];


uint8_t bpskQ[4] = {216,3,1,20};

uint8_t qpsknum[3] = {72,171,62};

uint8_t qpskPreamble[2]={201,99};


uint8_t qamnum[8] = {16,50,84,118,152,186,220,254};

int32_t rrc_Coefficients[31] = {150, -281, -668, -589, 98, 1042, 1507, 851,
                     -891, -2765, -3230, -1048, 3886, 10117, 15446, 17504,
                     15446, 10177, 3886, -1048, -3230, -2765, -891, 851,
                     1507, 1042, 98, -589, -668, -281, 150};

uint8_t bpskstore[8];

uint8_t qpskstore[120];

uint8_t etpskstore[90];


uint8_t qamstore[60];

int16_t arraybuffI[31];

int16_t arraybuffQ[31];

int16_t bI[2] = {GAIN_I,-GAIN_I};

int16_t bQ[2] = {0,0};

int16_t qpskI[4] = {GAIN_I,-GAIN_I,-GAIN_I,GAIN_I};

int16_t qpskQ[4] = {GAIN_Q,GAIN_Q,-GAIN_Q,-GAIN_Q};

int16_t etpskI[8] = {GAIN_I,H_GAIN,0,-H_GAIN,-GAIN_I,-H_GAIN,0,H_GAIN};

int16_t etpskQ[8] = {0,H_GAIN,GAIN_Q,H_GAIN,0,-H_GAIN,-GAIN_Q,-H_GAIN};

int16_t qamI[16] = {-GAIN_Q,-H_16QAM_GAIN,H_16QAM_GAIN,GAIN_Q,
                    -GAIN_Q,-H_16QAM_GAIN,H_16QAM_GAIN,GAIN_Q,
                    -GAIN_Q,-H_16QAM_GAIN,H_16QAM_GAIN,GAIN_Q,
                    -GAIN_Q,-H_16QAM_GAIN,H_16QAM_GAIN,GAIN_Q};

int16_t qamQ[16] = {GAIN_Q,GAIN_Q,GAIN_Q,GAIN_Q,
                    H_16QAM_GAIN,H_16QAM_GAIN,H_16QAM_GAIN,H_16QAM_GAIN,
                    -H_16QAM_GAIN,-H_16QAM_GAIN,-H_16QAM_GAIN,-H_16QAM_GAIN,
                    -GAIN_Q,-GAIN_Q,-GAIN_Q,-GAIN_Q};

//int dataArray[] = {1, 0, 1, 1, 0, 1};
char str1[100];

//Struct for holding UI Information
typedef struct USER_DATA
{
    char buffer [MAX_CHARS+1];
    uint8_t fieldCount;
    uint8_t fieldPosition[MAX_FIELDS];
    char fieldType[MAX_FIELDS];
}USER_DATA;

//-----------------------------------------------------------------------------
// Subroutines
//-----------------------------------------------------------------------------



void initTimer()
{

        // Enable clocks
      SYSCTL_RCGCTIMER_R |= SYSCTL_RCGCTIMER_R1;
      _delay_cycles(3);

      //Configure Timer 1 as the time base
      TIMER1_CTL_R &= ~TIMER_CTL_TAEN;                 // turn-off timer before reconfiguring
      TIMER1_CFG_R = TIMER_CFG_32_BIT_TIMER;           // configure as 32-bit timer (A+B)
      TIMER1_TAMR_R = TIMER_TAMR_TAMR_PERIOD;           // configure for periodic mode (count down)
      TIMER1_TAILR_R = 400;                             // set load value to match sample rate
      TIMER1_IMR_R = TIMER_IMR_TATOIM;                  // turn-on interrupts for timeout in timer module
      TIMER1_CTL_R |= TIMER_CTL_TAEN;
      enableNvicInterrupt(INT_TIMER1A);
}

void writeRegister(uint16_t opcode)
{
    setPinValue(CS,0);

    writeSpi0Data(opcode);
    readSpi0Data();


    setPinValue(CS,1);
    setPinValue(LDAC,0);
    setPinValue(LDAC,1);

}



void writeDAC(uint16_t opcode1,uint16_t opcode2)
{
    setPinValue(CS,0);


     SSI0_DR_R = DAC_A | opcode1;
     SSI0_DR_R = DAC_B | opcode2;

     setPinValue(CS,1);
     setPinValue(LDAC,0);
     setPinValue(LDAC,1);
}

void setSymbolRate(uint32_t fs){
    TIMER1_CTL_R &= ~TIMER_CTL_TAEN;                 // turn-off timer before reconfiguring
    TIMER1_TAILR_R = round(40e6/fs);
    TIMER1_CTL_R |= TIMER_CTL_TAEN;
}

void shiftFun(int16_t realI,int16_t realQ)
{
    uint8_t x = 0;
//shitf array right
//    for(x=0;x<59;x++)
//    {
//        arraybuff[x]=arraybuff[x+1];
//    }
//    arraybuff[60]=real;

    // shift array left
    for(x=31;x>0;x--)
        {
            arraybuffI[x]=arraybuffI[x-1];
            arraybuffQ[x]=arraybuffQ[x-1];
        }
        arraybuffI[0]=realI;
        arraybuffQ[0]=realQ;
}

void correlation(){
    uint8_t i = 0;
    int32_t corrI = 0,corrQ = 0;

    for(i = 0; i < 31; i++){
        //have to multiply and add x(t)rrc(t)
       corrI += arraybuffI[i]*rrc_Coefficients[i];
       corrQ += arraybuffQ[i]*rrc_Coefficients[i];
    }

    corrI =corrI/65536;
//    snprintf(str1, sizeof(str1), "CorrI:%d\n", corrI);
//    putsUart0(str1);
    corrQ =corrQ/65536;
//    snprintf(str1, sizeof(str1), "CorrQ:%d\n", corrQ);
//    putsUart0(str1);
    writeDAC(2151+corrI*3,2151+corrQ*3);
}


void getbit(uint8_t index,uint8_t size)
{
    uint8_t x;
    uint8_t inx = bpskQ[index];
    uint8_t val = 0;
    //IF SIZE = 1 then do bpsk bit extraction
    if(size == 1){
        for( x = 0; x<8;x++)
        {
            val = inx & 1;
            snprintf(str1, sizeof(str1), "value of bit:%d\n", val);
            putsUart0(str1);
            bpskstore[x]= val;
            inx = inx >> 1;
        }
    }else if(size == 2){
        uint8_t t;
        for(t = 0; t<2 ; t++)
        {
            uint8_t intx = qpskPreamble[t];
            for( x = 0; x<4;x++)
                            {
                                val = intx & 3;
                                snprintf(str1, sizeof(str1), "value of bit:%d\n", val);
                                putsUart0(str1);
                                qpskstore[x+(t*4)]= val;
                                intx = intx >> 2;
                            }
        }

    }else if(size == 3){
        uint8_t t;

        for(t=0;t<30;t++)
        {
            uint8_t intx = random[t];
            for( x = 0; x<3;x++)
            {
                if((x+t) == 8)
                {

                }
                else if(x == 2)
                {
                    val = intx & 3;
                    val = val << 1;
                    val = val & 6;
                    snprintf(str1, sizeof(str1), "value of bit:%d\n", val);
                    putsUart0(str1);
                    etpskstore[x+(t*3)]= val;
                }
                else
                {
                    val = intx & 7;
                    snprintf(str1, sizeof(str1), "value of bit:%d\n", val);
                    putsUart0(str1);
                    etpskstore[x+(t*3)]= val;
                    intx = intx >> 3;
                }


            }

        }

    }
    else if(size == 4){
            uint8_t t;

            for(t=0;t<30;t++)
            {
                uint8_t inx = random[t];
                for( x = 0; x<2;x++)
                {
                    val = inx & 15;
                    snprintf(str1, sizeof(str1), "value of bit:%d\n", val);
                    putsUart0(str1);
                    qamstore[x+(t*2)]=val;
                    inx = inx >> 4;

                }
           }
    }
    //IF SIZE = 2 then do qpsk 2bit extraction
}





void setfreq(uint32_t f){
    frequency = f;
}

void symbolISR(){
    uint16_t x = 0;

    if(RRC)
    {

        starval = star % 4;
        if(starval == 0)
        {
            //send symbol
            if(bpskf == true)
            {
//                if(star ==32)
//                {
//                    uint8_t i = 0;
//                    for(i=0; i < 64; i++){
//                        snprintf(str1, sizeof(str1), "%d\n", arraybuff[i]);
//                        putsUart0(str1);
//                    }
//                }
               star = star % 32;
//               snprintf(str1, sizeof(str1), "star%d\n", star);
//               putsUart0(str1);
//               snprintf(str1, sizeof(str1), "bpskstore%d\n", bpskstore[star/4]);
//               putsUart0(str1);

               shiftFun(bI[bpskstore[star/4]],bQ[bpskstore[star/4]]);
               correlation();

            }
            if(qpskf == true){
                star = star % 480;
                shiftFun(qpskI[qpskstore[star/4]],qpskQ[qpskstore[star/4]]);
                correlation();


            }
            if(eightpskf == true){
                            star = star % 360;
                            shiftFun(etpskI[etpskstore[star/4]],etpskQ[etpskstore[star/4]]);
                            correlation();

           }
            if(qamf == true){
                star = star % 240;
                shiftFun(qamI[qamstore[star/4]],qamQ[qamstore[star/4]]);
                correlation();
                        }
        }
        else
        {
                            //send zero
            shiftFun(0,0);
            correlation();
        }

        star++;
            setPinValue(CS,1);
            TIMER1_ICR_R = TIMER_ICR_TATOCINT;
    }
    else
    {
        if(dummy == true){

                //snprintf(str1, sizeof(str1), "delta value:%d\n", deltaPhase);
                //putsUart0(str1);
                phi_Index += deltaPhase;
                deltaPhase_A = (phi_Index >> 20);
                //deltaPhase_B = ((phi_Index + (4294967295/4) ) >> 20);
                deltaPhase_B = ((phi_Index + 1073741824 ) >> 20);
                writeDAC(sineLut[deltaPhase_A],sineLut[deltaPhase_B]);

            }
            if(sineChannelA == true){
               phi_Index += deltaPhase;
               deltaPhase_B = ((phi_Index + (4294967295/4) ) >> 20);
               x = DAC_A | sineLut[deltaPhase_B];
               SSI0_DR_R = x;
            }
            if(sineChannelB == true){
                   phi_Index += deltaPhase;
                   deltaPhase_B = ((phi_Index + (4294967295/4) ) >> 20);
                   x = DAC_A | sineLut[deltaPhase_B];
                   SSI0_DR_R = x;
                }
            if(bpskf == true)
            {

                if(bpskstore[star]==0)
                {
                   // writeDAC(sineLut[1024],sineLut[2151]); // first index should be the positive .5, second param should be 0
                    writeDAC(sineLut[1024],sineLut[2082]);
                }
                else
                {
                    writeDAC(sineLut[3052],sineLut[2082]); // first index should be -.5, second param should be 0
                }
                star++;

                star = star % 8 ;
                bytes = bytes % 4;
            }
            if(qpskf == true){

                star++;
                star = star % 480 ;
                bytes = bytes % 4;
                       writeDAC(2151+qpskI[qpskstore[star]],2151+qpskQ[qpskstore[star]]);

            }
            if(eightpskf == true){

                //bytes = bytes % 4;
                writeDAC(2151+etpskI[etpskstore[star]],2151+etpskQ[etpskstore[star]]);
                star++;
                star = star % 360 ;
            }
            if(qamf == true){
                writeDAC(2151+qamI[qamstore[star]],2151+qamQ[qamstore[star]]);
                star++;
                star = star % 240 ;
            }if(clipping == true){
                phi_Index += deltaPhase;
                                deltaPhase_A = (phi_Index >> 20);
                                //deltaPhase_B = ((phi_Index + (4294967295/4) ) >> 20);
                                deltaPhase_B = ((phi_Index + 1073741824 ) >> 20);
                                writeDAC(sineLut[deltaPhase_A],sineLut[deltaPhase_B]);

            }

            setPinValue(CS,1);
            TIMER1_ICR_R = TIMER_ICR_TATOCINT;
    }




}




uint16_t readRegister(uint16_t opcode, uint16_t regAdd)
{
    setPinValue(CS,0);

    writeSpi0Data(opcode);
    readSpi0Data();

    writeSpi0Data(regAdd);
    readSpi0Data();

    writeSpi0Data(0x00);
    uint16_t pin = readSpi0Data();

    setPinValue(CS,1);
    return pin;
}

// Initialize Hardware
void initHw()
{
    // Initialize system clock to 40 MHz
    initSystemClockTo40Mhz();


}




// Function to get a string from UART0
void getsUart0(USER_DATA* data) {
    char c;
    uint8_t count = 0;

    while (1) {
        // Get a character from UART0
        c = getcUart0();

        // Handle backspace
        if (c == 8 || c == 127) {
           // putsUart0("backspace");
            if (count > 0) {
                count--;
            }
        }
        // Handle carriage return
        else if (c == 13) {
            //putsUart0("carriage");
            data->buffer[count] = '\0';  // Add null terminator
            return;  // Exit the function
        }
        // Handle space or printable character
        else if (c >= 32) {
            // Store the character in the buffer
            data->buffer[count] = c;
            count++;

            // Check if the buffer is full
            if (count == MAX_CHARS) {
                data->buffer[count] = '\0';  // Add null terminator
                return;  // Exit the function
            }
        }
    }
}

//

void parseFields(USER_DATA *userData) {
    uint8_t i=0;
    uint8_t index=0;
    char current_char;
    bool prevChar = true;
    userData->fieldCount = 0;
    while(userData->buffer[i]){
        //if(prevChar){
        current_char = userData->buffer[i];
        if(ALPHA(current_char)){
            if(prevChar){
                userData->fieldCount++;
                userData->fieldType[index] = 'a';
                userData->fieldPosition[index] = i;
                //userData->fieldPosition[index] = next;
                //next++;
                //putsUart0("alpha\n");
                prevChar = false;
                index++;
            }
        }else if(IS_NUM(current_char)){
           if(prevChar){
                userData->fieldCount++;
                userData->fieldType[index] = 'n';
                userData->fieldPosition[index] = i;
                //userData->fieldPosition[index] = next;
                //next++;
                index++;
                //putsUart0("numeric\n");
                prevChar = false;
           }
        }else{                       //userData->fieldType[index] = 'd';
             userData->buffer[i] = '\0';
             //putsUart0("Delimiter\n");
             prevChar = true;
        }
        i++;
    }
}

char* getFieldString(USER_DATA* data, uint8_t fieldNumber){
    if(fieldNumber <= data->fieldCount){
        return &(data->buffer[data->fieldPosition[fieldNumber-1]]);
        //putsUart0("works\n");
    }
   return NULL;
}

int32_t myAtoi(char* str)
{
    int32_t result = 0;
    // Initialize sign as positive
    int sign = 1;

    int i = 0;

    // If number is negative,
    // then update sign
    if (str[0] == '-') {
        sign = -1;

        // Also update index of first digit
        i++;
    }

    // Iterate through all digits
    // and update the result
    for (; str[i] != '\0'; ++i)
        result = result * 10 + str[i] - '0';

    // Return result with sign
    return sign * result;
}

int32_t getFieldInteger(USER_DATA* data, uint8_t fieldNumber){
    int32_t val;
    if(fieldNumber <= data->fieldCount && (data->fieldType[fieldNumber] == 'n')){
        val = myAtoi(&data->buffer[data->fieldPosition[fieldNumber]]);
        //return (&data->buffer[data->fieldPosition[fieldNumber-1]]);
        //putsUart0("works\n");
      return val;
    }
   return 0;
}

int my_strcmp(const char *a, const char *b) {
    while (*a && *a == *b) {
        ++a;
        ++b;
    }
    return (int)(unsigned char)(*a) - (int)(unsigned char)(*b);
}

bool isCommand(USER_DATA* data, const char strCommand[], uint8_t minArguments) {
    uint8_t argCount = (data->fieldCount)-1;
    uint8_t string_result;
    char *str;
    str = getFieldString(data,1);
    string_result = my_strcmp(str,strCommand);
    if((string_result == 0) && argCount >= minArguments){
        //putsUart0("More than 2\n");
        return true;
    }else{
        //putsUart0("less than 2\n");
        return false;
    }

}






//-----------------------------------------------------------------------------
// Main
//-----------------------------------------------------------------------------

int main(void)
{

    USER_DATA data;



    // Initialize hardware
    initHw();
    initSpi0(1);
    initUart0();
    initTimer();
    uint8_t i;
    uint16_t x;
    // Setup UART0 baud rate

    setPinValue(CS,1);

    setUart0BaudRate(115200, 40e6);
    setSpi0BaudRate(20e6, 40e6);
    selectPinPushPullOutput(LDAC);
    srand(time(NULL));
    uint32_t phase = 0;

    //Initialize LUT


    uint16_t j = 0;
    for(j = 0; j < LUT_SIZE; j++)
    {

        sinVal = ((float)j/4096.0)*(2.0*PI);
        sinVal = sin(sinVal);
        sineLut[j] = 2151+1944*(sinVal);        //zero volts @ 2151

    }

    for(j = 0; j < 30; j++)
       {

            random[j]=rand() % 256;
            snprintf(str1, sizeof(str1), "num %d:%d\n", j,random[j]);
            putsUart0(str1);

       }

    setPinValue(LDAC,1);

    while(true)
    {
        putsUart0("Enter key\n");
        getsUart0(&data);
        //putsUart0(data.buffer);
        parseFields(&data);
        for(i = 0; i < data.fieldCount; i++){
                    putcUart0(data.fieldType[i]);
                    putcUart0('\t');
                    putsUart0(&data.buffer[data.fieldPosition[i]]);
                    putcUart0('\n');
                }

        if(isCommand(&data,"writea",1))
        {
            putsUart0("Call A\n");
            int16_t dataVal = getFieldInteger(&data,1);
            snprintf(str1, sizeof(str1), "value:%d\n", dataVal);
            putsUart0(str1);
            x = 0x3000 | dataVal;
            writeRegister(x);

        }

        if(isCommand(&data,"writeb",1))
                {
                    putsUart0("Call B\n");
                    int16_t dataVal = getFieldInteger(&data,1);
                    snprintf(str1, sizeof(str1), "value:%d\n", dataVal);
                    putsUart0(str1);
                    x = 0xB000 | dataVal;
                    writeRegister(x);
                }

        if(isCommand(&data,"freq",1))
                        {

                            int32_t dataVal = getFieldInteger(&data,1);
                            snprintf(str1, sizeof(str1), "setting freq:%d\n", dataVal);
                            putsUart0(str1);
                            setfreq(dataVal);
                        }



        if(isCommand(&data,"sinwave",0))
                     {
                         putsUart0("Sin wave B\n");
                         //phase = (2^32)*(0.1);
                         phase = 2e6;
                         uint16_t value = phase >> 20;
                         //int16_t frequency = getFieldInteger(&data,1);
                         snprintf(str1, sizeof(str1), "frequency:%d\n", value);
                         putsUart0(str1);
                         //period = data
                         //x = 0xB000 | dataVal;
                        // writeRegister(x);
                         uint16_t x;
                         uint16_t dataval;
                         for(x=2048;x>0;x--)
                         {
                             dataval = 0xB000 | x;
                             writeRegister(dataval);
                             waitMicrosecond(100);
                         }
                         waitMicrosecond(10000);
                         for(x=0;x<4095;x++)
                         {
                             dataval = 0xB000 | x;
                             writeRegister(dataval);
                             waitMicrosecond(100);
                         }
                         waitMicrosecond(10000);
                         for(x=4095;x>2048;x--)
                         {
                             dataval = 0xB000 | x;
                             writeRegister(dataval);
                             waitMicrosecond(100);
                         }
                     }
        if(isCommand(&data,"dummy",0))
        {
            uint16_t j = 0;
            for(j = 0; j < LUT_SIZE; j++)
            {

                sinVal = ((float)j/4096.0)*(2.0*PI);
                sinVal = sin(sinVal);
                sineLut[j] = 2151+1944*(sinVal);        //zero volts @ 2151

            }

            putsUart0("dummy 10k wave B\n");
            deltaPhase = (uint32_t)((frequency) * (1.0/fs) * (4294967295));

            RRC = 0;
            dummy = 1;
            sineChannelB = 0;
            sineChannelA = 0;
            bpskf = 0;
            qpskf = 0;
            eightpskf = 0;
            qamf = 0;
            clipping = 0;

            }

        if(isCommand(&data,"sine",0) && ((my_strcmp(getFieldString(&data,2),"q")==0)))
        {
            dummy = 0;
            sineChannelB = 0;
            sineChannelA = 1;
            bpskf = 0;
            qpskf = 0;
            eightpskf = 0;
            qamf = 0;
            clipping = 0;

                    putsUart0("Sin wave B\n");
                    deltaPhase = (uint32_t)((frequency) * (1.0/fs) * (4294967295));
        }

        if(isCommand(&data,"stop",0))
        {
                uint32_t sampleR = round(40e6/fs);
                setSymbolRate(sampleR);
                RRC = 0;
                dummy = 0;
                sineChannelB = 0;
                sineChannelA = 0;
                bpskf = 0;
                qpskf = 0;
                eightpskf = 0;
                qamf = 0;
                clipping = 0;
        }
        if(isCommand(&data,"bpsk",0))
        {
            //test
            //int data_length = sizeof(dataArray)/sizeof(dataArray[0]);
            getbit(bytes,1);
            RRC = 0;
            dummy = 0;
            sineChannelB = 0;
            sineChannelA = 0;
            bpskf = 1;
            qpskf = 0;
            eightpskf = 0;
            qamf = 0;
            clipping = 0;
        }
        if(isCommand(&data,"qpsk",0))
        {
            //getbit extract 2 bits at a time
            getbit(bytes,2);
            RRC = 0;
            star = 0;
            dummy = 0;
            sineChannelB = 0;
            sineChannelA = 0;
            bpskf = 0;
            qpskf = 1;
            eightpskf = 0;
            qamf = 0;
            clipping = 0;
        }
        if(isCommand(&data,"qam8",0))
        {
            getbit(bytes,3);
            RRC = 0;
            star = 0;
            //setSymbolRate(10);
            dummy = 0;
            sineChannelB = 0;
            sineChannelA = 0;
            bpskf = 0;
            qpskf = 0;
            eightpskf = 1;
            qamf = 0;
            clipping = 0;
        }
        if(isCommand(&data,"qam16",0))
        {
            getbit(bytes,4);
            RRC = 0;
            star = 0;
            dummy = 0;
            sineChannelB = 0;
            sineChannelA = 0;
            bpskf = 0;
            qpskf = 0;
            eightpskf = 0;
            qamf = 1;
            clipping = 0;

        }
        if(isCommand(&data,"sym",1))
                               {

                                   int32_t dataVal = getFieldInteger(&data,1);
                                   snprintf(str1, sizeof(str1), "Symbol rate set to:%d\n", dataVal);
                                   putsUart0(str1);
                                   setSymbolRate(dataVal);
                               }

        if(isCommand(&data,"cosine",0))
                               {
                                   putsUart0("cosine wave B\n");


                                   for(j = 0; j < LUT_SIZE; j++)
                                        {
//                                       snprintf(str1, sizeof(str1), "Cosine value:%d\n", cosineLut[j]);
//                                       putsUart0(str1);
                                       //WRITE TO DAC
                                       x = 0xB000 | (sineLut[j]);
                                       writeRegister(x);
                                       //SSI0_DR_R;
                                       waitMicrosecond(100);

                                        }


                               }

        //RRC ON Commands
        if(isCommand(&data,"rrcbpsk",0))
                               {

                                   getbit(bytes,1);
                                   RRC = 1;
                                              star = 0;
                                              dummy = 0;
                                              sineChannelB = 0;
                                              sineChannelA = 0;
                                              bpskf = 1;
                                              qpskf = 0;
                                              eightpskf = 0;
                                              qamf = 0;
                                              clipping = 0;



                               }
        if(isCommand(&data,"rrcqpsk",0))
                               {

                                   getbit(bytes,2);
                                   RRC = 1;
                                           star = 0;
                                              dummy = 0;
                                              sineChannelB = 0;
                                              sineChannelA = 0;
                                              bpskf = 0;
                                              qpskf = 1;
                                              eightpskf = 0;
                                              qamf = 0;
                                              clipping = 0;




                               }
        if(isCommand(&data,"rrcqpsk8",0))
        {

            getbit(bytes,3);
            RRC = 1;
            star = 0;
            dummy = 0;
            sineChannelB = 0;
            sineChannelA = 0;
            bpskf = 0;
            qpskf = 0;
            eightpskf = 1;
            qamf = 0;
            clipping = 0;


       }
        if(isCommand(&data,"rrcqam16",0))
                {

                    getbit(bytes,4);

                    RRC = 1;
                    clipping = 0;
                    star = 0;
                    dummy = 0;
                    sineChannelB = 0;
                    sineChannelA = 0;
                    bpskf = 0;
                    qpskf = 0;
                    eightpskf = 0;
                    qamf = 1;



               }
        if(isCommand(&data,"clip",1))
                       {

                          int32_t dataVal = getFieldInteger(&data,1);
                          snprintf(str1, sizeof(str1), "amplitude:%d\n", dataVal);

                          clipToAmplitude = dataVal/ 1000.0;

                          //Linearization formula y = - 0.0002x + 0.5328
                          //2nd linearization adapted and calibrated from new data y = -0.00025x + 0.5323
                          //example of algorithm  - 1-take the limit to were clipping needs to be. i.e take mVolts on this example imagine setting clipping to 400 mV
                          //step 2 -  convert mVolts to decimals. Divide by 1000.0 the units will become 0.40
                          //step 3 - find lower limit DAC unit by setting "Y" = 0.40 and solve linearization for "X".
                          //step 4 - find upper limit DAC unit by setting "Y" = -0.40 and solve linearization for "X"
                          //step 5 - read DAC unit from array if DAC unit Greater than or equal to LowerLimitX and lower than UpperLimitX, then Write to DAC
                          //Notes to implement, taking mV to clip and finding limits needs to happen before entering the ISR.






                          clipUpperLimit = (uint16_t)(-1 * (clipToAmplitude + b_Intercept)/m_Slope);
                          clipLowerLimit =(uint16_t)(-1 * (-clipToAmplitude + b_Intercept)/m_Slope);

                          snprintf(str1, sizeof(str1), "Lower limit:%d\n Upper limit:%d\n", clipLowerLimit,clipUpperLimit);
                          putsUart0(str1);

                          uint16_t j = 0;
                          for(j = 0; j < LUT_SIZE; j++)
                          {

                              sinVal = ((float)j/4096.0)*(2.0*PI);
                              sinVal = sin(sinVal);
                              sineLut[j] = 2151+1944*(sinVal);        //zero volts @ 2151

                              if(sineLut[j] >= (clipUpperLimit+500))
                              {
                                  sineLut[j] = clipUpperLimit+500;

                              }
                              else if(sineLut[j] <= (clipLowerLimit))
                              {
                                  sineLut[j] = clipLowerLimit;
                              }


                          }

                          deltaPhase = (uint32_t)((frequency) * (1.0/fs) * (4294967295));
                           RRC = 0;
                           star = 0;
                           dummy = 0;
                           sineChannelB = 0;
                           sineChannelA = 0;
                           bpskf = 0;
                           qpskf = 0;
                           eightpskf = 0;
                           qamf = 0;

                           clipping = 1;
                      }


    }
}
