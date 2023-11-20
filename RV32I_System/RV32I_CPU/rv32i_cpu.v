//
//  Author: Prof. Taeweon Suh
//          Computer Science & Engineering
//          Korea University
//  Date: July 14, 2020
//  Description: Skeleton design of RV32I Single-cycle CPU
//

`timescale 1ns/1ns
`define simdelay 1

module rv32i_cpu (
		      input         clk, reset,
            output [31:0] pc,		  		// program counter for instruction fetch
            input  [31:0] inst, 			// incoming instruction
            output        Memwrite, 	// 'memory write' control signal
            output [31:0] Memaddr,  	// memory address 
            output [31:0] MemWdata, 	// data to write to memory
            input  [31:0] MemRdata); 	// data read from memory

  wire        auipc, lui;
  wire        alusrc, regwrite;
  wire [4:0]  alucontrol;
  wire        memtoreg, memwrite;
  wire        branch, jal, jalr;

  assign Memwrite = memwrite ;

  // Instantiate Controller
  controller i_controller(
      .opcode		(inst[6:0]), 
		.funct7		(inst[31:25]), 
		.funct3		(inst[14:12]), 
		.auipc		(auipc),
		.lui			(lui),
		.memtoreg	(memtoreg),
		.memwrite	(memwrite),
		.branch		(branch),
		.alusrc		(alusrc),
		.regwrite	(regwrite),
		.jal			(jal),
		.jalr			(jalr),
		.alucontrol	(alucontrol));

  // Instantiate Datapath
  datapath i_datapath(
		.clk				(clk),
		.reset			(reset),
		.auipc			(auipc),
		.lui				(lui),
		.memtoreg		(memtoreg),
		.memwrite		(memwrite),
		.branch			(branch),
		.alusrc			(alusrc),
		.regwrite		(regwrite),
		.jal				(jal),
		.jalr				(jalr),
		.alucontrol		(alucontrol),
		.pc				(pc),
		.inst				(inst),
		.aluout			(Memaddr), 
		.MemWdata		(MemWdata),
		.MemRdata		(MemRdata));

endmodule


//
// Instruction Decoder 
// to generate control signals for datapath
//
module controller(input  [6:0] opcode,
                  input  [6:0] funct7,
                  input  [2:0] funct3,
                  output       auipc,
                  output       lui,
                  output       alusrc,
                  output [4:0] alucontrol,
                  output       branch,
                  output       jal,
                  output       jalr,
                  output       memtoreg,
                  output       memwrite,
                  output       regwrite);

	maindec i_maindec(
		.opcode		(opcode),
		.auipc		(auipc),
		.lui			(lui),
		.memtoreg	(memtoreg),
		.memwrite	(memwrite),
		.branch		(branch),
		.alusrc		(alusrc),
		.regwrite	(regwrite),
		.jal			(jal),
		.jalr			(jalr));

	aludec i_aludec( 
		.opcode     (opcode),
		.funct7     (funct7),
		.funct3     (funct3),
		.alucontrol (alucontrol));


endmodule


//
// RV32I Opcode map = Inst[6:0]
//
`define OP_R			7'b0110011
`define OP_I_ARITH	7'b0010011
`define OP_I_LOAD  	7'b0000011
`define OP_I_JALR  	7'b1100111
`define OP_S			7'b0100011
`define OP_B			7'b1100011
`define OP_U_LUI		7'b0110111
`define OP_J_JAL		7'b1101111
//
// Main decoder generates all control signals except alucontrol 
//
//
module maindec(input  [6:0] opcode,
               output       auipc,
               output       lui,
               output       regwrite,
               output       alusrc,
               output       memtoreg, memwrite,
               output       branch, 
               output       jal,
               output       jalr);

  reg [8:0] controls;

  assign {auipc, lui, regwrite, alusrc, 
			 memtoreg, memwrite, branch, jal, 
			 jalr} = controls;

  always @(*)
  begin
    case(opcode)
      `OP_R: 			controls <= #`simdelay 9'b0010_0000_0; // R-type
      `OP_I_ARITH: 	controls <= #`simdelay 9'b0011_0000_0; // I-type Arithmetic
      `OP_I_LOAD: 	controls <= #`simdelay 9'b0011_1000_0; // I-type Load
      `OP_S: 			controls <= #`simdelay 9'b0001_0100_0; // S-type Store
      `OP_B: 			controls <= #`simdelay 9'b0000_0010_0; // B-type Branch
      `OP_U_LUI: 		controls <= #`simdelay 9'b0111_0000_0; // LUI
      `OP_J_JAL: 		controls <= #`simdelay 9'b0011_0001_0; // JAL
      `OP_I_JALR:   controls <= #`simdelay 9'b0011_0000_1; // JALR
      default:    	controls <= #`simdelay 9'b0000_0000_0; // ???
    endcase
  end

endmodule

module forwarding_unit(
    input wire [4:0] ID_EX_Rs1,       // 현재 EX 스테이지의 Rs1
    input wire [4:0] ID_EX_Rs2,       // 현재 EX 스테이지의 Rs2
    input wire [4:0] EX_MEM_Rd,       // MEM 스테이지의 Rd
    input wire EX_MEM_RegWrite,       // MEM 스테이지의 레지스터 쓰기 신호 (RegWrite)
    input wire [4:0] MEM_WB_Rd,       // WB 스테이지의 Rd
    input wire MEM_WB_RegWrite,       // WB 스테이지의 레지스터 쓰기 신호 (RegWrite)
    output reg [1:0] ForwardA,        // Rs1을 위한 포워딩 제어 신호
    output reg [1:0] ForwardB         // Rs2를 위한 포워딩 제어 신호
);

    always @(*) begin
        // 초기 포워딩 신호 값 설정: No forwarding
        ForwardA = 2'b00;
        ForwardB = 2'b00;

        // EX/MEM -> ID/EX Forwarding (ALU 결과에서 EX 스테이지로 포워딩)
        if (EX_MEM_RegWrite && (EX_MEM_Rd != 0) && (EX_MEM_Rd == ID_EX_Rs1)) begin
            ForwardA = 2'b10;
        end
        if (EX_MEM_RegWrite && (EX_MEM_Rd != 0) && (EX_MEM_Rd == ID_EX_Rs2)) begin
            ForwardB = 2'b10;
        end

        // MEM/WB -> ID/EX Forwarding (Write Back 데이터에서 EX 스테이지로 포워딩)
        // MEM 스테이지에서 포워딩할 조건이 없을 때만 체크
        if (MEM_WB_RegWrite && (MEM_WB_Rd != 0) && !(EX_MEM_RegWrite && (EX_MEM_Rd != 0) && (EX_MEM_Rd == ID_EX_Rs1)) && (MEM_WB_Rd == ID_EX_Rs1)) begin
            ForwardA = 2'b01;
        end
        if (MEM_WB_RegWrite && (MEM_WB_Rd != 0) && !(EX_MEM_RegWrite && (EX_MEM_Rd != 0) && (EX_MEM_Rd == ID_EX_Rs2)) && (MEM_WB_Rd == ID_EX_Rs2)) begin
            ForwardB = 2'b01;
        end
    end

endmodule

module hazard_detection_unit(
    input wire [4:0] IF_ID_Rs1,        // Decode 스테이지의 첫 번째 소스 레지스터
    input wire [4:0] IF_ID_Rs2,        // Decode 스테이지의 두 번째 소스 레지스터
    input wire [4:0] ID_EX_Rd,         // EX 스테이지의 대상 레지스터
    input wire ID_EX_MemRead,          // EX 스테이지의 메모리 읽기 신호
    output reg PCWrite,                // PC 카운터 쓰기 신호
    output reg IF_ID_Write,            // IF/ID 파이프라인 레지스터 쓰기 신호
    output reg Control_Signals_Stall   // 컨트롤 신호 스톨
);

    initial begin
        PCWrite = 1;
        IF_ID_Write = 1;
        Control_Signals_Stall = 0;
    end

    always @(*) begin
        // Load-Use 하자드 검출: EX 스테이지에서 메모리 읽기가 발생하고 있고,
        // ID 스테이지의 소스 레지스터 중 하나가 해당 메모리 읽기의 대상 레지스터와 일치할 경우
        if (ID_EX_MemRead && ((ID_EX_Rd == IF_ID_Rs1) || (ID_EX_Rd == IF_ID_Rs2))) begin
            // 스톨 발생
            PCWrite = 0;               // 다음 명령어 인출을 중지
            IF_ID_Write = 0;           // 파이프라인 레지스터 업데이트 중지
            Control_Signals_Stall = 1; // 컨트롤 신호 스톨 활성화
        end else begin
            // 스톨이 필요 없으면 정상 동작
            PCWrite = 1;
            IF_ID_Write = 1;
            Control_Signals_Stall = 0;
        end
    end

endmodule

module pipeline_control_unit(
    input [6:0] opcode,        // 입력 opcode
    output reg pc_mux_ctl      // PC 제어 신호
);

// 여기에서 사용할 opcode 상수 정의
// 이 값들은 실제 RISC-V나 다른 아키텍처에 따라 다를 수 있습니다.
localparam OPCODE_BRANCH = 7'b1100011;
localparam OPCODE_JAL    = 7'b1101111;
localparam OPCODE_JALR   = 7'b1100111;
// ... 기타 필요한 opcode 상수 추가

// PC 제어 로직
always @(*) begin
    case (opcode)
        OPCODE_BRANCH,
        OPCODE_JAL,
        OPCODE_JALR: pc_mux_ctl = 1'b1;  // 분기 또는 점프 명령어의 경우
        default:     pc_mux_ctl = 1'b0;  // 기타 명령어의 경우
    endcase
end

endmodule

module pipeline_reg_IF_ID(
    input clk,
    input reset,
    input [31:0] instr_in,  // Instruction memory 에서 온 명령어
    input [31:0] pc_in,     // Program counter 에서 온 값
    input stall,            // Hazard Detection Unit 에서 온 스톨 신호
    output reg [31:0] instr_out,  // 명령어 레지스터 출력
    output reg [31:0] pc_out      // 프로그램 카운터 레지스터 출력
);

    always @(posedge clk or posedge reset) begin
        if (reset) begin
            // Reset 신호가 활성화되면 레지스터 초기화
            instr_out <= 0;
            pc_out <= 0;
        end else if (!stall) begin
            // 스톨이 아니면 입력 데이터 저장
            instr_out <= instr_in;
            pc_out <= pc_in;
        end
        // 스톨 상황에서는 레지스터 값 변경하지 않음
    end
endmodule

module pipeline_reg_ID_EX(
    input clk,
    input reset,
    input stall,                 // HDU로부터 오는 스톨 신호
    input [31:0] pc_in,          // IF 단계에서 오는 PC 값
    input [31:0] inst_in,        // IF 단계에서 오는 인스트럭션
    input [31:0] se_imm_in,      // Decode 단계에서 오는 sign-extended 신호
    output reg [31:0] pc_out,    // PC 값 출력
    output reg [31:0] inst_out,  // 인스트럭션 출력
    output reg [31:0] se_imm_out // sign-extended 신호 출력
);

    always @(posedge clk or posedge reset) begin
        if (reset) begin
            pc_out <= 0;
            inst_out <= 0;
            se_imm_out <= 0;
        end else if (!stall) begin
            pc_out <= pc_in;
            inst_out <= inst_in;
            se_imm_out <= se_imm_in;
        end
        // 스톨 상태에서는 출력 레지스터 값을 변경하지 않음
    end
endmodule




module pipeline_reg_EX_MEM(
    input clk,
    input reset,
    input [31:0] pc_in,             // EX 스테이지의 PC 값
    input regwrite_in,              // EX 스테이지의 RegWrite 컨트롤 신호
    input memtoreg_in,              // EX 스테이지의 MemtoReg 컨트롤 신호
    input memwrite_in,              // EX 스테이지의 MemWrite 컨트롤 신호
    input [31:0] aluresult_in,      // EX 스테이지의 ALU 결과
    input [31:0] writedata_in,      // EX 스테이지의 쓰기 데이터
    input [4:0] rd_in,              // EX 스테이지의 목적지 레지스터 주소
    output reg [31:0] pc_out,       // MEM 스테이지의 PC 값
    output reg regwrite_out,        // MEM 스테이지의 RegWrite 컨트롤 신호
    output reg memtoreg_out,        // MEM 스테이지의 MemtoReg 컨트롤 신호
    output reg memwrite_out,        // MEM 스테이지의 MemWrite 컨트롤 신호
    output reg [31:0] aluresult_out,// MEM 스테이지의 ALU 결과
    output reg [31:0] writedata_out,// MEM 스테이지의 쓰기 데이터
    output reg [4:0] rd_out         // MEM 스테이지의 목적지 레지스터 주소
);

    always @(posedge clk or posedge reset) begin
        if (reset) begin
            // Reset 시 모든 출력 레지스터를 0으로 초기화
            {pc_out, regwrite_out, memtoreg_out, memwrite_out, 
             aluresult_out, writedata_out, rd_out} <= 0;
        end else begin
            // 다음 스테이지에 전달될 값들을 레지스터에 업데이트
            pc_out <= pc_in;
            regwrite_out <= regwrite_in;
            memtoreg_out <= memtoreg_in;
            memwrite_out <= memwrite_in;
            aluresult_out <= aluresult_in;
            writedata_out <= writedata_in;
            rd_out <= rd_in;
        end
    end

endmodule


module pipeline_reg_MEM_WB(
    input clk,
    input reset,
    input [31:0] pc_in,               // MEM 스테이지의 PC 값
    input regwrite_in,                // MEM 스테이지의 RegWrite 컨트롤 신호
    input memtoreg_in,                // MEM 스테이지의 MemtoReg 컨트롤 신호
    input [31:0] aluresult_in,        // MEM 스테이지의 ALU 계산 결과
    input [31:0] readdata_in,         // MEM 스테이지에서 읽은 데이터
    input [4:0] rd_in,                // MEM 스테이지의 목적지 레지스터 주소
    output reg [31:0] pc_out,         // WB 스테이지의 PC 값
    output reg regwrite_out,          // WB 스테이지의 RegWrite 컨트롤 신호
    output reg memtoreg_out,          // WB 스테이지의 MemtoReg 컨트롤 신호
    output reg [31:0] aluresult_out,  // WB 스테이지로 넘어갈 ALU 계산 결과
    output reg [31:0] readdata_out,   // WB 스테이지로 넘어갈 메모리에서 읽은 데이터
    output reg [4:0] rd_out           // WB 스테이지의 목적지 레지스터 주소
);

    always @(posedge clk or posedge reset) begin
        if (reset) begin
            // 리셋 상태에서는 모든 출력 레지스터를 0으로 초기화
            {pc_out, regwrite_out, memtoreg_out, aluresult_out,
             readdata_out, rd_out} <= 0;
        end else begin
            // 다음 스테이지로 전달될 값들을 레지스터에 업데이트
            pc_out <= pc_in;
            regwrite_out <= regwrite_in;
            memtoreg_out <= memtoreg_in;
            aluresult_out <= aluresult_in;
            readdata_out <= readdata_in;
            rd_out <= rd_in;
        end
    end

endmodule





//
// ALU decoder generates ALU control signal (alucontrol)
//
module aludec(input      [6:0] opcode,
              input      [6:0] funct7,
              input      [2:0] funct3,
              output reg [4:0] alucontrol);

  always @(*)

    case(opcode)

      `OP_R:   		// R-type
		begin
			case({funct7,funct3})
			 10'b0000000_000: alucontrol <= #`simdelay 5'b00000; // addition (add)
			 10'b0100000_000: alucontrol <= #`simdelay 5'b10000; // subtraction (sub)
			 10'b0000000_111: alucontrol <= #`simdelay 5'b00001; // and (and)
			 10'b0000000_110: alucontrol <= #`simdelay 5'b00010; // or (or)
       10'b0000000_100: alucontrol <= #`simdelay 5'b00011; // xor (xor)
          default:         alucontrol <= #`simdelay 5'bxxxxx; // ???
        endcase
		end

      `OP_I_ARITH:   // I-type Arithmetic
		begin
			case(funct3)
			 3'b000:  alucontrol <= #`simdelay 5'b00000; // addition (addi)
			 3'b110:  alucontrol <= #`simdelay 5'b00010; // or (ori)
			 3'b111:  alucontrol <= #`simdelay 5'b00001; // and (andi)
       3'b100: alucontrol <= #`simdelay 5'b00011; // xori
          default: alucontrol <= #`simdelay 5'bxxxxx; // ???
        endcase
		end

      `OP_I_LOAD: 	// I-type Load (LW, LH, LB...)
      	alucontrol <= #`simdelay 5'b00000;  // addition 

      `OP_B:    // B-type Branch (BEQ, BNE, ...)
    begin
      case(funct3)
        // ... (Other funct3 cases for different branches)
        // 3'b111: alucontrol <= #`simdelay 5'b00110; // bgeu (Assuming alucontrol signal for bgeu is `00110`)
        // The default case could be for subtraction as most branch comparisons are subtractions
        default: alucontrol <= #`simdelay 5'b10000; // subtraction (used for BEQ, BNE, etc.)
      endcase
    end

      `OP_S:   		// S-type Store (SW, SH, SB)
      	alucontrol <= #`simdelay 5'b00000;  // addition 

      `OP_U_LUI: 		// U-type (LUI)
      	alucontrol <= #`simdelay 5'b00000;  // addition

      default: 
      	alucontrol <= #`simdelay 5'b00000;  // 

    endcase
    
endmodule



//
// RV32I Opcode map = Inst[6:0]
//
`define OP_R			7'b0110011
`define OP_I_ARITH	7'b0010011
`define OP_I_LOAD  	7'b0000011
`define OP_I_JALR  	7'b1100111
`define OP_S			7'b0100011
`define OP_B			7'b1100011
`define OP_U_LUI		7'b0110111
`define OP_J_JAL		7'b1101111
//
// CPU datapath
//
module datapath(input         clk, reset,
                input  [31:0] inst,
                input         auipc,
                input         lui,
                input         regwrite,
                input         memtoreg,
                input         memwrite,
                input         alusrc, 
                input  [4:0]  alucontrol,
                input         branch,
                input         jal,
                input         jalr,

                output reg [31:0] pc,
                output [31:0] aluout,
                output [31:0] MemWdata,
                input  [31:0] MemRdata);

  wire [4:0]  rs1, rs2, rd;
  wire [2:0]  funct3;
  wire [31:0] rs1_data, rs2_data;
  reg  [31:0] rd_data;
  wire [20:1] jal_imm;
  wire [31:0] se_jal_imm;
  wire [12:1] br_imm;
  wire [31:0] se_br_imm;
  wire [31:0] se_imm_itype;
  wire [31:0] se_imm_stype;
  wire [31:0] auipc_lui_imm;
  reg  [31:0] alusrc1;
  reg  [31:0] alusrc2;
  wire [31:0] branch_dest;
  wire [31:0] jal_dest;
  wire [31:0] jalr_dest;
  wire		  Nflag, Zflag, Cflag, Vflag;
  wire		  f3beq, f3blt;
  wire		  beq_taken;
  wire		  blt_taken;
  wire      f3bgeu;
  wire      bgeu_taken;


  assign rs1 = inst[19:15];
  assign rs2 = inst[24:20];
  assign rd  = inst[11:7];
  assign funct3  = inst[14:12];

  //
  // PC (Program Counter) logic 
  //
  assign f3beq  = (funct3 == 3'b000);
  assign f3blt  = (funct3 == 3'b100);
  assign f3bgeu = (funct3 == 3'b111);

  assign beq_taken  =  branch & f3beq & Zflag;
  assign blt_taken  =  branch & f3blt & (Nflag != Vflag);
  assign bgeu_taken =  branch & f3bgeu & Cflag;

  assign branch_dest = (pc + se_br_imm);
  assign jal_dest 	= (pc + se_jal_imm);
  assign jalr_dest   = {aluout[31:1],1'b0};


  // JAL immediate
  assign jal_imm[20:1] = {inst[31],inst[19:12],inst[20],inst[30:21]};
  assign se_jal_imm[31:0] = {{11{jal_imm[20]}},jal_imm[20:1],1'b0};

  // Branch immediate
  assign br_imm[12:1] = {inst[31],inst[7],inst[30:25],inst[11:8]};
  assign se_br_imm[31:0] = {{19{br_imm[12]}},br_imm[12:1],1'b0};

  // ###### SungWun Jeon : Start ######
  
    // Forwarding Unit에 필요한 와이어 선언
    wire        ex_mem_regwrite; // EX/MEM 파이프라인 레지스터로부터 온 WB 제어 신호
    wire [4:0]  ex_mem_rd;       // EX/MEM 파이프라인 레지스터로부터 온 rd
    wire        mem_wb_regwrite; // MEM/WB 파이프라인 레지스터로부터 온 WB 제어 신호
    wire [4:0]  mem_wb_rd;       // MEM/WB 파이프라인 레지스터로부터 온 rd
    wire [4:0]  id_ex_rs1;       // ID/EX 파이프라인 레지스터로부터 온 rs1
    wire [4:0]  id_ex_rs2;       // ID/EX 파이프라인 레지스터로부터 온 rs2
    wire [1:0]  fwd_a;           // Forwarding Unit으로부터 ALU 입력 A에 대한 포워딩 신호
    wire [1:0]  fwd_b;           // Forwarding Unit으로부터 ALU 입력 B에 대한 포워딩 신호
    
    // Forwarding Unit 모듈 인스턴스화
    forwarding_unit FU(
    .EX_MEM_RegWrite(ex_mem_regwrite), // 변경: .ex_mem_regwrite -> .EX_MEM_RegWrite
    .EX_MEM_Rd(ex_mem_rd),             // 변경: .ex_mem_rd -> .EX_MEM_Rd
    .MEM_WB_RegWrite(mem_wb_regwrite), // 변경: .mem_wb_regwrite -> .MEM_WB_RegWrite
    .MEM_WB_Rd(mem_wb_rd),             // 변경: .mem_wb_rd -> .MEM_WB_Rd
    .ID_EX_Rs1(id_ex_rs1),             // 변경: .id_ex_rs1 -> .ID_EX_Rs1
    .ID_EX_Rs2(id_ex_rs2),             // 변경: .id_ex_rs2 -> .ID_EX_Rs2
    .ForwardA(fwd_a),                  // 변경: .fwd_a -> .ForwardA
    .ForwardB(fwd_b)                   // 변경: .fwd_b -> .ForwardB
);
	// ###### SungWun Jeon : End ######
	 
	 // ###### SungWun Jeon : Start ######
	 
		// Datapath 내 필요한 와이어와 신호 선언
    wire [4:0]   if_id_rs1, if_id_rs2;      // IF/ID 레지스터로부터의 rs1, rs2
    wire [4:0]   id_ex_rd;                  // ID/EX 레지스터로부터의 rd
    wire         id_ex_memread;             // ID/EX 단계의 MemRead 신호
    wire         hd_pc_write, hd_if_id_write, hd_control_mux_sel;  // Hazard Detection Unit의 출력
    
    // ... 여기에 파이프라인 레지스터와 인스트럭션 메모리 등 기타 Datapath 구성 요소들

    // Hazard Detection Unit 인스턴스화
hazard_detection_unit hdu(
    .IF_ID_Rs1(if_id_rs1),             // 변경: .if_id_rs1 -> .IF_ID_Rs1
    .IF_ID_Rs2(if_id_rs2),             // 변경: .if_id_rs2 -> .IF_ID_Rs2
    .ID_EX_Rd(id_ex_rd),               // 변경: .id_ex_rd -> .ID_EX_Rd
    .ID_EX_MemRead(id_ex_memread),     // 변경: .id_ex_memread -> .ID_EX_MemRead
    .PCWrite(hd_pc_write),             // 변경: .pc_write -> .PCWrite
    .IF_ID_Write(hd_if_id_write),      // 변경: .if_id_write -> .IF_ID_Write
    .Control_Signals_Stall(hd_control_mux_sel) // 변경: .control_mux_sel -> .Control_Signals_Stall
);

	 // ###### SungWun Jeon : End ######
	 
	 // ###### SungWun Jeon : Start ######
	 
	 wire [6:0] opcode = inst[6:0];
    wire pc_mux_ctl; 
    wire [31:0] branch_target_address; // 분기 목표 주소 계산
    wire [31:0] jump_target_address;   // JAL 점프 목표 주소 계산
    wire [31:0] jalr_target_address;   // JALR 목표 주소 계산
    wire [31:0] next_pc;               // 다음 PC 계산
    
    pipeline_control_unit PCU(
        .opcode(opcode),
        .pc_mux_ctl(pc_mux_ctl)
    );

    // 분기 목표 주소 계산
    assign br_imm[12:1] = {inst[31], inst[7], inst[30:25], inst[11:8]};
    assign branch_target_address = pc + {{19{br_imm[12]}}, br_imm, 1'b0};
    assign jump_target_address = pc + {{11{jal_imm[20]}}, jal_imm};

    // JALR Target Address 계산 (rs1에서 읽은 값을 가져와야 함)
    assign jalr_target_address = (rs1_data + {{20{inst[31]}}, inst[31:20]}) & ~1;

	 
	//
// RV32I Opcode map = Inst[6:0]
//
`define OP_R			7'b0110011
`define OP_I_ARITH	7'b0010011
`define OP_I_LOAD  	7'b0000011
`define OP_I_JALR  	7'b1100111
`define OP_S			7'b0100011
`define OP_B			7'b1100011
`define OP_U_LUI		7'b0110111
`define OP_J_JAL		7'b1101111
    // 다음 PC 계산 로직
    always @(posedge clk, posedge reset) begin
    if (reset) begin
        pc <= 32'b0;
    end else begin
        if (pc_mux_ctl) begin
            case (opcode)
                7'b1100011: pc <= branch_target_address; // 상황에 따른 주소 변경
                7'b1101111: pc <= jump_target_address;    // 다른 상황에 따른 주소 변경
                7'b1100111: pc <= jalr_target_address;   // 지정된 상황에 따른 주소 변경
                // ... 기타 분기/점프 조건
                default: pc <= pc + 32'd4; // 기본적으로 주소 증가
            endcase
        end else if (beq_taken | blt_taken | bgeu_taken) begin
            pc <= branch_dest; // 분기가 취해진 경우
        end else if (jal) begin
            pc <= jal_dest; // JAL 명령어가 실행된 경우
        end else if (jalr) begin
            pc <= jalr_dest; // JALR 명령어가 실행된 경우
        end else begin
            pc <= pc + 32'd4; // 그 외의 경우, 다음 명령어로 진행
        end
    end
end
	 // ###### SungWun Jeon : End ######
  
  // 
  // Register File 
  //
  regfile i_regfile(
    .clk			(clk),
    .we			(regwrite),
    .rs1			(rs1),
    .rs2			(rs2),
    .rd			(rd),
    .rd_data	(rd_data),
    .rs1_data	(rs1_data),
    .rs2_data	(rs2_data));


	assign MemWdata = rs2_data;


	//
	// ALU 
	//
	alu i_alu(
		.a			(alusrc1),
		.b			(alusrc2),
		.alucont	(alucontrol),
		.result	(aluout),
		.N			(Nflag),
		.Z			(Zflag),
		.C			(Cflag),
		.V			(Vflag));

	// 1st source to ALU (alusrc1)
	always@(*)
	begin
		if      (auipc)	alusrc1[31:0]  =  pc;
		else if (lui) 		alusrc1[31:0]  =  32'b0;
		else          		alusrc1[31:0]  =  rs1_data[31:0];
	end
	
	// 2nd source to ALU (alusrc2)
	always@(*)
	begin
		if	     (auipc | lui)			alusrc2[31:0] = auipc_lui_imm[31:0];
		else if (alusrc & memwrite)	alusrc2[31:0] = se_imm_stype[31:0];
		else if (alusrc)					alusrc2[31:0] = se_imm_itype[31:0];
		else									alusrc2[31:0] = rs2_data[31:0];
	end
	
	assign se_imm_itype[31:0] = {{20{inst[31]}},inst[31:20]};
	assign se_imm_stype[31:0] = {{20{inst[31]}},inst[31:25],inst[11:7]};
	assign auipc_lui_imm[31:0] = {inst[31:12],12'b0};


	// Data selection for writing to RF
	always@(*)
	begin
		if	     (jal)			rd_data[31:0] = pc + 4;
		else if (memtoreg)	rd_data[31:0] = MemRdata;
		else						rd_data[31:0] = aluout;
	end
	
	
	// ###### SungWun Jeon : Start ######
	// IF/ID 파이프라인 레지스터에서 필요한 신호들을 선언합니다.
wire [31:0] if_id_next_pc;
wire [31:0] if_id_instruction;
wire        if_id_write;       // IF/ID 레지스터에 쓰기 제어 신호
wire        if_id_flush;       // IF/ID 레지스터를 초기화하는 신호

// IF/ID 파이프라인 레지스터의 인스턴스 생성
pipeline_reg_IF_ID if_id_reg(
    .clk(clk),
    .reset(reset),
    .instr_in(inst),              // 변경: instruction_in -> instr_in
    .pc_in(pc + 4),               // 변경: next_pc_in -> pc_in
    .stall(!if_id_write),         // 변경: write_enable -> stall (논리 반전 필요)
    .instr_out(if_id_instruction), // 변경: instruction_out -> instr_out
    .pc_out(if_id_next_pc)         // 변경: next_pc_out -> pc_out
);


// 예시 신호 정의 (이 부분은 실제 회로에 따라 다를 수 있습니다)
wire [31:0] if_id_pc_out;         // IF/ID 단계의 PC 출력
wire [31:0] if_id_instruction_out; // IF/ID 단계의 인스트럭션 출력
wire [31:0] se_imm;               // sign-extended된 즉시값
wire id_ex_stall;                 // 스톨 신호

// 실제 출력 신호 (ID/EX 레지스터 출력)
wire [31:0] id_ex_pc;
wire [31:0] id_ex_inst;
wire [31:0] id_ex_se_imm;

// pipeline_reg_ID_EX 인스턴스화
pipeline_reg_ID_EX id_ex_reg(
    .clk(clk),
    .reset(reset),
    .stall(id_ex_stall),
    .pc_in(if_id_pc_out),
    .inst_in(if_id_instruction_out),
    .se_imm_in(se_imm),
    .pc_out(id_ex_pc),
    .inst_out(id_ex_inst),
    .se_imm_out(id_ex_se_imm)
);


// ... EX 단계 로직 ...

// EX/MEM 파이프라인 레지스터에서 필요한 신호들을 선언합니다.
	wire [31:0] ex_mem_pc;          // EX/MEM 파이프라인 레지스터의 PC 출력
	wire ex_mem_memtoreg;           // EX/MEM 파이프라인 레지스터의 MemtoReg 신호 출력
	wire ex_mem_memwrite;           // EX/MEM 파이프라인 레지스터의 MemWrite 신호 출력
	wire [31:0] ex_mem_aluresult;   // EX/MEM 파이프라인 레지스터의 ALU 결과 출력
	wire [31:0] ex_mem_writedata;   // EX/MEM 파이프라인 레지스터의 쓰기 데이터 출력

// EX/MEM 파이프라인 레지스터의 인스턴스 생성
pipeline_reg_EX_MEM ex_mem_reg(
    .clk(clk),
    .reset(reset),
    .pc_in(id_ex_pc),            // ID/EX 파이프라인 레지스터에서 가져온 PC 값
    .regwrite_in(id_ex_regwrite),// EX 단계의 RegWrite 신호
    .memtoreg_in(id_ex_memtoreg),// EX 단계의 MemtoReg 신호
    .memwrite_in(id_ex_memwrite),// EX 단계의 MemWrite 신호
    .aluresult_in(aluout),       // ALU의 결과 값
    .writedata_in(id_ex_rs2_data), // 메모리에 쓸 데이터 (EX 단계의 rs2_data 출력)
    .rd_in(id_ex_rd),            // RD (Destination Register) 값

    // EX/MEM 파이프라인 레지스터의 출력 단자
    .pc_out(ex_mem_pc),
    .regwrite_out(ex_mem_regwrite),
    .memtoreg_out(ex_mem_memtoreg),
    .memwrite_out(ex_mem_memwrite),
    .aluresult_out(ex_mem_aluresult),
    .writedata_out(ex_mem_writedata),
    .rd_out(ex_mem_rd)
);



// ... MEM 단계 로직 ...

// MEM/WB 파이프라인 레지스터를 위한 wire 신호들 정의
wire [31:0] mem_wb_pc;            // MEM/WB 파이프라인 레지스터의 PC 출력
wire mem_wb_memtoreg;             // MEM/WB 파이프라인 레지스터의 MemtoReg 신호 출력
wire [31:0] mem_wb_aluresult;     // MEM/WB 파이프라인 레지스터의 ALU 결과 출력
wire [31:0] mem_wb_readdata;      // MEM/WB 파이프라인 레지스터의 메모리 읽기 데이터 출력

// MEM/WB 파이프라인 레지스터의 인스턴스 생성
pipeline_reg_MEM_WB mem_wb_reg(
    .clk(clk),
    .reset(reset),
    .pc_in(ex_mem_pc),             // EX/MEM 파이프라인 레지스터에서 가져온 PC 값
    .regwrite_in(ex_mem_regwrite), // MEM 단계의 RegWrite 신호
    .memtoreg_in(ex_mem_memtoreg), // MEM 단계의 MemtoReg 신호
    .aluresult_in(ex_mem_aluresult), // ALU의 결과 값
    .readdata_in(mem_read_data),   // 메모리 읽기 데이터 (MEM 단계의 출력)
    .rd_in(ex_mem_rd),             // RD (Destination Register) 값

    .pc_out(mem_wb_pc),
    .regwrite_out(mem_wb_regwrite),
    .memtoreg_out(mem_wb_memtoreg),
    .aluresult_out(mem_wb_aluresult),
    .readdata_out(mem_wb_readdata),
    .rd_out(mem_wb_rd)
);

	// ###### SungWun Jeon : End ######
	
endmodule
