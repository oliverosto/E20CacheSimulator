/*
CS-UY 2214
sim.cpp
*/
//OLIVER OSTOJIC

#include <cstddef>
#include <iostream>
#include <string>
#include <fstream>
#include <iomanip>
#include <vector>
#include <regex>
#include <cstdlib>
#include <cstdint>

using namespace std;
// this struct will be used to implement the LRU policy
struct block {
    int timestamp = 0;
    int tag = -1;
};

int find_LRU_block (vector<vector<block>> L1, int row, int cols) {
    int lru_index = 0;
    // this finds the highest index, a high index indicates block was not used recently
    for (int i = 1; i < cols; ++i) {
        if (L1[row][i].timestamp > L1[row][lru_index].timestamp) {
            lru_index = i;
        }
    }
    return lru_index;
}
void print_log_entry(const string &cache_name, const string &status, int pc, int addr, int row) {
    cout << left << setw(8) << cache_name + " " + status <<  right <<
        " pc:" << setw(5) << pc <<
        "\taddr:" << setw(5) << addr <<
        "\trow:" << setw(4) << row << endl;
}

void update_cache_lw (vector<vector<block>> &L1, int row, int cols, int tag, int pc, uint16_t &addr, const string cache, bool &hit) {
    int col_index = 0; // to be used for where hit is
    int prev_pc = pc - 1;
    for (int i = 0; i < cols; ++i) {
        if (L1[row][i].tag == tag) {
            hit = true;
            col_index = i;
            break;
        }
    }
    if (hit) {
        print_log_entry(cache, "HIT", prev_pc, addr, row);
        // Update timestamp
        for (int i = 0; i < cols; ++i) {
            if (i != col_index) {
                L1[row][i].timestamp += 1;
            }
        }
    }
    else {
        print_log_entry(cache, "MISS", prev_pc, addr, row);
        int lru_index = find_LRU_block(L1, row, cols);
        L1[row][lru_index].tag = tag;
        L1[row][lru_index].timestamp = 0; // reset timestamp to 0 bc used recently
        for (int i = 0; i < cols; ++i) {
            if (i != lru_index) {
                L1[row][i].timestamp += 1;
            }
        }
    }
}

void update_cache_sw (vector<vector<block>> &L1, int row, int cols, int tag, int pc, uint16_t &addr, const string cache) {
    int prev_pc = pc - 1;
    print_log_entry(cache, "SW", prev_pc, addr, row);
    int lru_index = find_LRU_block(L1, row, cols);
    L1[row][lru_index].tag = tag;
    L1[row][lru_index].timestamp = 0; // reset timestamp to 0 bc used recently
    for (int i = 0; i < cols; ++i) {
        if (i != lru_index) {
            L1[row][i].timestamp += 1;
        }
    }
}
                
int execute_instruction(uint16_t &pc, uint16_t R[], uint16_t mem[], bool &running, uint16_t &addr) {
    //Initialize Variables
    uint16_t opcode, rA, rB, rDst, imm7, imm13, last4bits;
    uint16_t temp_pc = pc & 8191;
    opcode = mem[temp_pc] >> 13;
    rA = (mem[temp_pc] >> 10) & 7;
    rB = (mem[temp_pc] >> 7) & 7;
    rDst = (mem[temp_pc] >> 4) & 7;
    last4bits = mem[temp_pc] & 0b1111;
    imm7 = mem[temp_pc] & 0b1111111;
    imm13 = mem[temp_pc] & 0b1111111111111;
    // for LW and SW
    addr = (R[rA] + imm7) & 8191;
    //sign extend imm7
    uint16_t bit7 = (mem[temp_pc] >> 6) & 1;
    if (bit7 == 1) {
        imm7 = imm7 ^ 0b1111111110000000;
    }
    // Execute add
    if (opcode == 0b000 && last4bits == 0b0000) {
        if (rDst != 0) {
            R[rDst] = R[rA] + R[rB];
        }
        pc += 1;
    }
    // Execute sub
    else if (opcode == 0b000 && last4bits == 0b0001) {
        if (rDst != 0) {
            R[rDst] = R[rA] - R[rB];
        }
        pc += 1;
    }
    // Execute or
    else if (opcode == 0b000 && last4bits == 0b0010) {
        if (rDst != 0) {
            R[rDst] = R[rA] | R[rB];
        }
        pc += 1;
    }
    // Execute and
    else if (opcode == 0b000 && last4bits == 0b0011) {
        if (rDst != 0) {
            R[rDst] = R[rA] & R[rB];
        }
        pc += 1;
    }
    // Execute slt
    else if (opcode == 0b000 && last4bits == 0b0100) {
        if (rDst != 0) {
            if (R[rA] < R[rB]) {
                R[rDst] = 1;
            }
            else {
                R[rDst] = 0;
            }
        }
        pc += 1;
    }
    // Execute jr
    else if (opcode == 0b000 && last4bits == 0b1000) {
        if (pc == R[rA]) {
            running = false;
        }
        else {
            pc = R[rA];
        }
    }
    // Execute slti
    else if (opcode == 0b111) {
        if (rB != 0) {
            if (R[rA] < imm7) {
                R[rB] = 1;
            }
            else {
                R[rB] = 0;
            }
        }
        pc += 1;
    }
    // Execute lw
    else if (opcode == 0b100) {
        if (rB != 0) {
            R[rB] = mem[addr]; // makes sure only last 13 bits are used as memory index
        }
        pc += 1;
    }
    // Execute sw
    else if (opcode == 0b101) {
        mem[addr] = R[rB]; // makes sure only last 13 bits are used as memory index
        pc += 1;
    }
    // Execute jeq
    else if (opcode == 0b110) {
        if (R[rA] == R[rB]) {
            pc = pc + 1 + imm7;
        }
        else {
            pc += 1;
        }
    }
    // Execute addi
    else if (opcode == 0b001) {
        if (rB != 0) {
            R[rB] = R[rA] + imm7;
        }
        pc += 1;
    }
    // Execute j
    else if (opcode == 0b010) {
        if (pc == imm13) {
            running = false;
        }
        else {
            pc = imm13;
        }
    }
    // Execute jal
    else if (opcode == 0b011) {
        if (pc == imm13) {
            running = false;
        }
        R[7] = pc + 1;
        pc = imm13;
    }
    else {
        running = false;
        cerr << "Invalid Opcode" << endl;
    }
    return opcode;
}
/*
    Prints out the correctly-formatted configuration of a cache.

    @param cache_name The name of the cache. "L1" or "L2"

    @param size The total size of the cache, measured in memory cells.
        Excludes metadata

    @param assoc The associativity of the cache. One of [1,2,4,8,16]

    @param blocksize The blocksize of the cache. One of [1,2,4,8,16,32,64])

    @param num_rows The number of rows in the given cache.
*/
void print_cache_config(const string &cache_name, int size, int assoc, int blocksize, int num_rows) {
    cout << "Cache " << cache_name << " has size " << size <<
        ", associativity " << assoc << ", blocksize " << blocksize <<
        ", rows " << num_rows << endl;
}

/*
    Prints out a correctly-formatted log entry.

    @param cache_name The name of the cache where the event
        occurred. "L1" or "L2"

    @param status The kind of cache event. "SW", "HIT", or
        "MISS"

    @param pc The program counter of the memory
        access instruction

    @param addr The memory address being accessed.

    @param row The cache row or set number where the data
        is stored.
*/

// Some helpful constant values that we'll be using.
size_t const static NUM_REGS = 8;
size_t const static MEM_SIZE = 1<<13;
size_t const static REG_SIZE = 1<<16;

/*
    Loads an E20 machine code file into the list
    provided by mem. We assume that mem is
    large enough to hold the values in the machine
    code file.

    @param f Open file to read from
    @param mem Array represetnting memory into which to read program
*/
void load_machine_code(ifstream &f, uint16_t mem[]) {
    regex machine_code_re("^ram\\[(\\d+)\\] = 16'b(\\d+);.*$");
    size_t expectedaddr = 0;
    string line;
    while (getline(f, line)) {
        smatch sm;
        if (!regex_match(line, sm, machine_code_re)) {
            cerr << "Can't parse line: " << line << endl;
            exit(1);
        }
        size_t addr = stoi(sm[1], nullptr, 10);
        unsigned instr = stoi(sm[2], nullptr, 2);
        if (addr != expectedaddr) {
            cerr << "Memory addresses encountered out of sequence: " << addr << endl;
            exit(1);
        }
        if (addr >= MEM_SIZE) {
            cerr << "Program too big for memory" << endl;
            exit(1);
        }
        expectedaddr ++;
        mem[addr] = instr;
    }
}

/*
    Prints the current state of the simulator, including
    the current program counter, the current register values,
    and the first memquantity elements of memory.

    @param pc The final value of the program counter
    @param regs Final value of all registers
    @param memory Final value of memory
    @param memquantity How many words of memory to dump
*/
void print_state(uint16_t pc, uint16_t regs[], uint16_t memory[], size_t memquantity) {
    cout << setfill(' ');
    cout << "Final state:" << endl;
    cout << "\tpc=" <<setw(5)<< pc << endl;

    for (size_t reg=0; reg<NUM_REGS; reg++)
        cout << "\t$" << reg << "="<<setw(5)<<regs[reg]<<endl;

    cout << setfill('0');
    bool cr = false;
    for (size_t count=0; count<memquantity; count++) {
        cout << hex << setw(4) << memory[count] << " ";
        cr = true;
        if (count % 8 == 7) {
            cout << endl;
            cr = false;
        }
    }
    if (cr)
        cout << endl;
}

/**
    Main function
    Takes command-line args as documented below
*/
int main(int argc, char *argv[]) {
    char *filename = nullptr;
    bool do_help = false;
    bool arg_error = false;
    string cache_config;
    for (int i=1; i<argc; i++) {
        string arg(argv[i]);
        if (arg.rfind("-",0)==0) {
            if (arg== "-h" || arg == "--help")
                do_help = true;
            else if (arg=="--cache") {
                i++;
                if (i>=argc)
                    arg_error = true;
                else
                    cache_config = argv[i];
            }
            else
                arg_error = true;
        } else {
            if (filename == nullptr)
                filename = argv[i];
            else
                arg_error = true;
        }
    }
    /* Display error message if appropriate */
    if (arg_error || do_help || filename == nullptr) {
        cerr << "usage " << argv[0] << " [-h] [--cache CACHE] filename" << endl << endl;
        cerr << "Simulate E20 cache" << endl << endl;
        cerr << "positional arguments:" << endl;
        cerr << "  filename    The file containing machine code, typically with .bin suffix" << endl<<endl;
        cerr << "optional arguments:"<<endl;
        cerr << "  -h, --help  show this help message and exit"<<endl;
        cerr << "  --cache CACHE  Cache configuration: size,associativity,blocksize (for one"<<endl;
        cerr << "                 cache) or"<<endl;
        cerr << "                 size,associativity,blocksize,size,associativity,blocksize"<<endl;
        cerr << "                 (for two caches)"<<endl;
        return 1;
    }

    
    ifstream f(filename);
    if (!f.is_open()) {
        cerr << "Can't open file "<<filename<<endl;
        return 1;
    }
    // TODO: your code here. Load f and parse using load_machine_code
    // INITIALIZING VARIABLES for E20 Simulator
    uint16_t mem[MEM_SIZE]{0}, R[8]{0};
    uint16_t pc = 0, addr;
    bool running = true;
    bool hit = false;
    load_machine_code(f, mem);
    
    // TODO: your code here. Do simulation.
    /* parse cache config */
    if (cache_config.size() > 0) {
        vector<int> parts;
        size_t pos;
        size_t lastpos = 0;
        while ((pos = cache_config.find(",", lastpos)) != string::npos) {
            parts.push_back(stoi(cache_config.substr(lastpos,pos)));
            lastpos = pos + 1;
        }
        parts.push_back(stoi(cache_config.substr(lastpos)));
        if (parts.size() == 3) {
            int L1size = parts[0];
            int L1assoc = parts[1];
            int L1blocksize = parts[2];
            // TODO: execute E20 program and simulate one cache here
            // CALCULATE ROWS
            int L1rows = L1size / (L1blocksize * L1assoc);
            print_cache_config("L1", L1size, L1assoc, L1blocksize, L1rows);
            // INITIALIZE CACHE
            vector<vector<block>>L1(L1rows, vector<block>(L1assoc));
            // SIMULATE ONE CACHE
            while (running) {
                int instr = execute_instruction(pc, R, mem, running, addr);
                int blockid = addr / L1blocksize;
                int row = blockid % L1rows;
                int block_tag = blockid / L1rows;
                // if instruction is LW
                if (instr == 0b100) {
                    hit = false;
                    update_cache_lw(L1, row, L1assoc, block_tag, pc, addr, "L1", hit);
                }
                // if instruction is SW
                else if (instr == 0b101) {
                    update_cache_sw (L1, row, L1assoc, block_tag, pc, addr, "L1");
                }
            }
        }
        else if (parts.size() == 6) {
            int L1size = parts[0];
            int L1assoc = parts[1];
            int L1blocksize = parts[2];
            int L2size = parts[3];
            int L2assoc = parts[4];
            int L2blocksize = parts[5];
            // TODO: execute E20 program and simulate two caches here
            // CALCULATE ROWS
            int L1rows = L1size / (L1blocksize * L1assoc);
            int L2rows = L2size / (L2blocksize * L2assoc);
            print_cache_config("L1", L1size, L1assoc, L1blocksize, L1rows);
            print_cache_config("L2", L2size, L2assoc, L2blocksize, L2rows);
            // INITIALIZE CACHES
            vector<vector<block>>L1(L1rows, vector<block>(L1assoc));
            vector<vector<block>>L2(L2rows, vector<block>(L2assoc));
            // SIMULATE TWO CACHES
            while (running) {
                int instr = execute_instruction(pc, R, mem, running, addr);
                // Find row and tag for L1
                int L1blockid = addr / L1blocksize;
                int L1row = L1blockid % L1rows;
                int L1block_tag = L1blockid / L1rows;

                // Find row and tag for L2
                int L2blockid = addr / L2blocksize;
                int L2row = L2blockid % L2rows;
                int L2block_tag = L2blockid / L2rows;

                
                // if instruction is LW
                if (instr == 0b100) {
                    hit = false;
                    update_cache_lw(L1, L1row, L1assoc, L1block_tag, pc, addr, "L1", hit);
                    if (!hit) {
                        update_cache_lw(L2, L2row, L2assoc, L2block_tag, pc, addr, "L2", hit);
                    }
                    
                }
                // if instruction is SW
                else if (instr == 0b101) {
                    update_cache_sw (L1, L1row, L1assoc, L1block_tag, pc, addr, "L1");
                    update_cache_sw (L2, L2row, L2assoc, L2block_tag, pc, addr, "L2");
                }
            }
        }
        else {
            cerr << "Invalid cache config"  << endl;
            return 1;
        }
    }
    
    // TODO: your code here. print the final state of the simulator before ending, using print_state
    
    return 0;
}
