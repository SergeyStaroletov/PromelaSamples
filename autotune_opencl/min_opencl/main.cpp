#include <CL/cl.h>
#include <locale.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <fstream>
#include <iostream>
#include <sys/types.h>
#include <sys/stat.h>
#include <sys/time.h>




void printfinfo() {
    char *value;
    size_t valueSize;
    cl_uint platformCount;
    clGetPlatformIDs(0, NULL, &platformCount);
    cl_platform_id *platforms =
        (cl_platform_id *)malloc(sizeof(cl_platform_id) * platformCount);
    clGetPlatformIDs(platformCount, platforms, NULL);
    for (int p = 0; p < platformCount; p++) {
        cl_uint deviceCount;
        clGetDeviceIDs(platforms[p], CL_DEVICE_TYPE_ALL, 0, NULL, &deviceCount);
        cl_device_id *devices =
            (cl_device_id *)malloc(sizeof(cl_device_id) * deviceCount);
        clGetDeviceIDs(platforms[p], CL_DEVICE_TYPE_ALL, deviceCount, devices,
                       NULL);
        for (int d = 0; d < deviceCount; d++) {
            clGetDeviceInfo(devices[d], CL_DEVICE_NAME, 0, NULL, &valueSize);
            value = (char *)malloc(valueSize);
            clGetDeviceInfo(devices[d], CL_DEVICE_NAME, valueSize, value, NULL);
            printf("%d. device: %s\n", d + 1, value);
            free(value);
            clGetDeviceInfo(devices[d], CL_DEVICE_VERSION, 0, NULL, &valueSize);
            value = (char *)malloc(valueSize);
            clGetDeviceInfo(devices[d], CL_DEVICE_VERSION, valueSize, value, NULL);
            printf(" %d.1 hardware standart: %s\n", d + 1, value);
            free(value);
            clGetDeviceInfo(devices[d], CL_DEVICE_OPENCL_C_VERSION, 0, NULL,
                            &valueSize);
            value = (char *)malloc(valueSize);
            clGetDeviceInfo(devices[d], CL_DEVICE_OPENCL_C_VERSION, valueSize, value,
                            NULL);
            printf(" %d.2 OpenCL C ver: %s\n", d + 1, value);
            free(value);
            cl_uint maxComputeUnits;
            clGetDeviceInfo(devices[d], CL_DEVICE_MAX_COMPUTE_UNITS,
                            sizeof(maxComputeUnits), &maxComputeUnits, NULL);
            printf(" %d.3 compute units: %d\n", d + 1, maxComputeUnits);
        }
        free(devices);
    }
    free(platforms);
}

//#define MAXSIZE 804864000
#define MAXSIZE (256000000/4)


void compute() {
    FILE *fff;

    int *array = (int *)malloc(MAXSIZE * sizeof(int));
    for (int i = 0; i < MAXSIZE; i++) {
        array[i] = 123 + rand() % 100000;
    }

    array[666666] = 64;

    cl_platform_id platform;
    cl_device_id device;
    cl_context context;
    cl_program program;
    cl_kernel kernel;
    cl_command_queue queue;
    FILE *programHandle;
    char *programBuffer;
    size_t programSize;
    clGetPlatformIDs(1, &platform, NULL);
    clGetDeviceIDs(platform, CL_DEVICE_TYPE_GPU, 1, &device, NULL);
    cl_uint units;
    clGetDeviceInfo(device, CL_DEVICE_MAX_COMPUTE_UNITS, sizeof(units), &units,
                    NULL);
    int *mins = (int *)malloc(units * sizeof(int));
    context = clCreateContext(NULL, 1, &device, NULL, NULL, NULL);
    programHandle = fopen("kern.cl", "r");

    fseek(programHandle, 0, SEEK_END);
    programSize = ftell(programHandle);
    rewind(programHandle);
    programBuffer = (char *)malloc(programSize + 1);
    memset(programBuffer, 0, programSize + 1);
    fread(programBuffer, sizeof(char), programSize, programHandle);
    fclose(programHandle);
    program = clCreateProgramWithSource(context, 1, (const char **)&programBuffer,
                                        &programSize, NULL);
    free(programBuffer);
    int err = clBuildProgram(program, 1, &device, "-cl-std=CL1.0", NULL, NULL);

    if (err != CL_SUCCESS) {
        printf("clBuildProgram: %d\n", err);
        char log[0x10000];
        clGetProgramBuildInfo(program, device, CL_PROGRAM_BUILD_LOG, 0x10000, log,
                              NULL);
        printf("\n%s\n", log);
        return;
    }


    //------- save ptx code
    cl_uint program_num_devices;
    clGetProgramInfo(program, CL_PROGRAM_NUM_DEVICES, sizeof(cl_uint),&program_num_devices, NULL);
    size_t binaries_sizes[program_num_devices];
    clGetProgramInfo(program, CL_PROGRAM_BINARY_SIZES, program_num_devices*sizeof(size_t),binaries_sizes, NULL);
    char **binaries = new char*[program_num_devices];
    for (size_t i = 0; i < program_num_devices; i++)
        binaries[i] = new char[binaries_sizes[i]+1];
    clGetProgramInfo(program, CL_PROGRAM_BINARIES, program_num_devices*sizeof(size_t), binaries, NULL);
    for (size_t i = 0; i < program_num_devices; i++)
    {
        binaries[i][binaries_sizes[i]] = '\0';
        std::cout << "Program " << i << ":" << std::endl;
        std::ofstream out_binary_file;
        char *fname = new char[20];
        strcpy(fname, "kernelX.bin");
        fname[6] = '0' + i;
        out_binary_file.open (fname);
        for (size_t s = 0; s < binaries_sizes[0]; s++)
            out_binary_file << binaries[0][s];
        out_binary_file.close();
        delete []fname;
    }
    //------

    err = 0;
    kernel = clCreateKernel(program, "findMinValue2", &err);

    queue = clCreateCommandQueue(context, device, 0, NULL);
    cl_mem clArray = clCreateBuffer(context, CL_MEM_READ_WRITE,
                                    MAXSIZE * sizeof(int), NULL, NULL);
    clEnqueueWriteBuffer(queue, clArray, CL_TRUE, 0, MAXSIZE * sizeof(int), array,
                         0, NULL, NULL);
    cl_mem clMins = clCreateBuffer(context, CL_MEM_READ_WRITE,
                                   units * sizeof(int), NULL, NULL);
    int chunkSize = MAXSIZE / units;
    cl_mem clChunkSize =
        clCreateBuffer(context, CL_MEM_READ_WRITE, sizeof(int), NULL, NULL);
    clEnqueueWriteBuffer(queue, clChunkSize, CL_TRUE, 0, sizeof(int), &chunkSize,
                         0, NULL, NULL);


    double mid_gb = 0;
    double mid_time = 0;

    int C = 5; //count of re-runs

    fff = fopen("out.csv", "w");
    if (!fff) printf("no file!");
    fprintf(fff, "Glob;SM;WG;TS;time;GB\n");

    printf("go\n");



    int SM = 10;
    int TS = 32;
    int WG = 128;
//here is a point to organize a loop
{
    int TS_real = MAXSIZE / (SM * WG) * TS;
    int WG_real = WG / TS;

    mid_time = 0;
    mid_gb= 0;

    for (int t = 0; t < C; t++) {


    size_t global_item_size = SM * WG_real;
    size_t local_item_size = WG_real;


    clSetKernelArg(kernel, 0, sizeof(cl_mem), &clArray) ;
    clSetKernelArg(kernel, 1, sizeof(cl_mem), &clMins);
    clSetKernelArg(kernel, 2, sizeof(cl_uint) * local_item_size, NULL);
    clSetKernelArg(kernel, 3, sizeof(cl_uint), &TS_real);
    //clSetKernelArg(kernel, 4, sizeof(cl_uint), &IC);


    struct timeval initial_time, final_time;
    gettimeofday(&initial_time, NULL);


    clEnqueueNDRangeKernel(queue, kernel, 1, NULL, &global_item_size,
                           &local_item_size, 0, NULL, NULL);


    clEnqueueReadBuffer(queue, clMins, CL_TRUE, 0, units * sizeof(int), mins, 0,
                        NULL, NULL);

    gettimeofday(&final_time, NULL);


    long long exec_time = ((long long)final_time.tv_sec * 1000000 + final_time.tv_usec) -
                          ((long long)initial_time.tv_sec * 1000000 + initial_time.tv_usec);

    printf("\nExecution time was %llu microseconds\n", exec_time);

    float bandwidth = 1e-9*(float)(MAXSIZE*sizeof(cl_uint)) /
                      ((float)exec_time/1e6);

    printf("Memory bandwidth %.2f GB/sec\n", bandwidth);


    mid_time += exec_time;
    mid_gb += bandwidth;


    int min = INT32_MAX;
    for (int i = 0; i < units; i++) {
     //  printf("analisyng min[%d] = %d\n", i, mins[i]);
        if (mins[i] < min) min = mins[i];
    }
    printf("Total min = %d\n", min);


    clEnqueueReadBuffer(queue, clArray, CL_TRUE, 0, MAXSIZE * sizeof(int), array,
                         0, NULL, NULL);


    clFlush(queue);

    }


    printf("Global size = %d; SM = %d; WG = %d; WG real= %d; TS = %d; TS real = %d; test(MAXSIZE) = %d(%d); time = %lf; gb = %lf \n\n", (SM * WG), SM, WG, WG_real, TS, TS_real, (TS_real * SM * WG_real), MAXSIZE,  mid_time / (C*1000), mid_gb / C);
    
    fprintf(fff, "%d;%d;%d;%d;%lf;%lf\n", (SM * WG), SM, WG, TS,  mid_time / (C * 1000), mid_gb / C);
    
}//loop

    fclose(fff);

    clFinish(queue);
    clReleaseKernel(kernel);
    clReleaseProgram(program);
    clReleaseMemObject(clArray);
    clReleaseMemObject(clMins);
    clReleaseCommandQueue(queue);
    clReleaseContext(context);
    return;
}

int main(int argc, const char *argv[]) {
    printfinfo();

    compute();

    return 0;
}
