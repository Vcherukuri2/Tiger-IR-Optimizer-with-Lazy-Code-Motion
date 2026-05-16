package middle_end;

import ir.*;
import ir.IRInstruction.OpCode;
import ir.datatype.*;
import ir.operand.*;

import java.util.*;

class BasicBlock {
private
    List<IRInstruction> instructions;
private
    List<BasicBlock> successors;
private
    List<BasicBlock> predecessors;
private
    boolean visited;
private int startLine;
private int endLine;
private IRFunction function;

    /** Internal phi representation: { "phi", destBaseOrSsa, src0, src1, ... } — not Tiger-IR. */
    private final List<String[]> phiNodes = new ArrayList<>();
    /** SSA-renamed instruction sequence for this block (parallel to CFG, not the flat file index). */
    private List<IRInstruction> ssaIRList = null;

    BasicBlock()
    {
        this.instructions = new ArrayList<>();
        this.successors = new ArrayList<>();
        this.predecessors = new ArrayList<>();
        this.visited = false;
        this.startLine = -1;
        this.endLine = -1;
    }

    BasicBlock(int startLine, int endLine, IRFunction function)
    {
        this.instructions = new ArrayList<>();
        this.successors = new ArrayList<>();
        this.predecessors = new ArrayList<>();
        this.visited = false;
        this.startLine = startLine;
        this.endLine = endLine;
        this.function = function;
    }

    void setStartLine(int startLine)
    {
        this.startLine = startLine;
    }

    void setEndLine(int endLine)
    {
        this.endLine = endLine;
    }

    void setFunction(IRFunction function)
    {
        this.function = function;
    }

    int getStartLine()
    {
        return startLine;
    }

    int getEndLine()
    {
        return endLine;
    }

    IRFunction getFunction()
    {
        return function;
    }

    void addInstruction(IRInstruction instruction)
    {
        instructions.add(instruction);
    }

    void addSuccessor(BasicBlock succ)
    {
        if (successors.contains(succ) == false)
            successors.add(succ);
    }

    void addPredecessor(BasicBlock pred)
    {
        if (predecessors.contains(pred) == false)
            predecessors.add(pred);
    }

    List<IRInstruction> getInstructions()
    {
        if (instructions.size() == 0) {
            List<IRInstruction> instuctionList = function.getInstructions();
            for (int i = startLine; i <= endLine; i++) {
                instructions.add(instuctionList.get(i));
            }
        }
        return instructions;
    }

    List<BasicBlock> getSuccessors()
    {
        return successors;
    }

    List<BasicBlock> getPredecessors()
    {
        return predecessors;
    }

    void setVisited(boolean visited)
    {
        this.visited = visited;
    }

    boolean isVisited()
    {
        return visited;
    }

    List<String[]> getPhiNodes() {
        return phiNodes;
    }

    List<IRInstruction> getSsaIRList() {
        return ssaIRList;
    }

    void setSsaIRList(List<IRInstruction> ssaIRList) {
        this.ssaIRList = ssaIRList;
    }

    /** Clear cached block IR, SSA phis, and SSA instruction list (call before CFG rebuild). */
    void clearSSAState() {
        instructions.clear();
        phiNodes.clear();
        ssaIRList = null;
    }

    @Override
    public boolean equals(Object obj) {
        if (obj == this) {
            return true;
        }
        if (!(obj instanceof BasicBlock)) {
            return false;
        }
        BasicBlock bb = (BasicBlock) obj;
        return startLine == bb.startLine && endLine == bb.endLine
                && function.name.equals(bb.function.name);
    }

}

public class CFG {
    public IRFunction function;
    public List<BasicBlock> basicBlocks;
    Map <Integer, BasicBlock> lineToBlock; //startLine to BasicBlock
    Map <String, BasicBlock> labelToBlock; //label to BasicBlock
    Map <IRInstruction, BasicBlock> instrToBlock; //instruction to BasicBlock

    /** Cached loop information (back edges, natural loops, nesting depth). Cleared on rebuildCFG. */
    private LoopAnalysis.LoopInfo cachedLoopInfo;


     public CFG(IRFunction function)
    {
        this.function = function;
        this.basicBlocks = new ArrayList<>();
        this.lineToBlock = new HashMap<>();
        this.labelToBlock = new HashMap<>();
        this.instrToBlock = new HashMap<>();
        buildCFG();
    }

    void buildCFG()
    {
        List<Integer> startLNs = new ArrayList<>();
        List<Integer> endLNs = new ArrayList<>();
        List<IRInstruction> instuctionList = function.getInstructions();
        int n = instuctionList.size();

        // leader instructions are:
        // 1. the first instruction of the program/function
        // 2. the target of a conditional or unconditional jump / goto -- label instruction
        // 3. the instruction following a jump/goto 
        startLNs.add(0);
        for (int i = 1;  i < n; i++) {
            // check if the instruction is a leader
            IRInstruction instr = instuctionList.get(i);
            switch (instr.opCode) {
                case LABEL:
                    // this instruction is a leader
                    if (startLNs.contains(i) == false)
                        startLNs.add(i);
                    break;
                
                case GOTO:
                case BREQ:
                case BRNEQ:
                case BRLT:
                case BRGT:
                case BRLEQ:
                case BRGEQ:
                    if (i + 1 < n) {
                        // next instruction is a leader
                        if (startLNs.contains(i+1) == false)
                            startLNs.add(i+1);
                        
                    }
                    break;
                default:    
                    // this instr is not a leader
            }
        }
        // dump all the leaders
        System.err.println("+=======================+");
        for (int i = 0; i < startLNs.size(); i++) {
            System.err.print(startLNs.get(i) + ", ");
        }
        System.err.println("");
        System.err.println("+=======================+");

        int v = startLNs.size();
        for (int i =0; i < v ; i++){
            int j = startLNs.get(i) + 1; // the next instruction
            while (j < n && startLNs.contains(j) == false) {
                j++;
            }
            j--;
            if (endLNs.contains(j) == false)
                endLNs.add(j);
            else {
                System.err.println("Error: end line already exists!!!!!!!!!!");
            }
        }
        
        // we have pairs of start and end lines of basic blocks

        for (int i = 0; i < v; i++) {
            BasicBlock bb = new BasicBlock(startLNs.get(i), endLNs.get(i), function);
            basicBlocks.add(bb);
            lineToBlock.put(startLNs.get(i), bb);
            if (instuctionList.get(startLNs.get(i)).opCode == OpCode.LABEL) {
                String label = ((IRLabelOperand) instuctionList.get(startLNs.get(i)).operands[0]).getName();
                labelToBlock.put(label, bb);
            }
        }

        // go over all tha basic blocks 
        for (BasicBlock bb : basicBlocks){
            int endLine = bb.getEndLine();
            IRInstruction currIns = instuctionList.get(endLine);            
                switch (currIns.opCode) {
                    case BREQ:
                    case BRNEQ:
                    case BRLT:
                    case BRGT:
                    case BRLEQ:
                    case BRGEQ:
                        String branch_label = ((IRLabelOperand) currIns.operands[0]).getName();
                        BasicBlock target_brnach = labelToBlock.get(branch_label);
                        bb.addSuccessor(target_brnach);
                        target_brnach.addPredecessor(bb);
                        if (endLine + 1 < n) {
                            target_brnach = lineToBlock.get(endLine + 1);
                            bb.addSuccessor(target_brnach);
                            target_brnach.addPredecessor(bb);
                            
                        }
                        break;
                    case GOTO:
                        String goto_lable = ((IRLabelOperand) currIns.operands[0]).getName();
                        BasicBlock target_goto = labelToBlock.get(goto_lable);
                        bb.addSuccessor(target_goto);
                        target_goto.addPredecessor(bb);
                        break;
                    default:    
                        if (endLine + 1 < n){
                            BasicBlock next_line = lineToBlock.get(endLine+1);
                            bb.addSuccessor(next_line);
                            next_line.addPredecessor(bb);
                        }
                }
        }

        //update map for instructions to basic blocks
        for (BasicBlock bb : basicBlocks){
            List<IRInstruction> instrList = bb.getInstructions();
            for (IRInstruction instr: instrList){
                instrToBlock.put(instr, bb);
            }
        }

    }

    /**
     * Recompute the CFG from {@link IRFunction#getInstructions()} after the flat instruction list
     * was rewritten. This is the canonical repair entry point: any pass that mutates
     * {@code function.instructions} should finish by calling {@code rebuildCFG()} (and, when
     * leaving SSA with {@code debug}, {@link #assertFlatInvariants()}).
     */
    public void rebuildCFG() {
        for (BasicBlock bb : basicBlocks) {
            bb.clearSSAState();
        }
        basicBlocks.clear();
        lineToBlock.clear();
        labelToBlock.clear();
        instrToBlock.clear();
        cachedLoopInfo = null;
        buildCFG();
    }

    /** @return cached {@link LoopAnalysis.LoopInfo}, or {@code null} if no pass has computed it yet. */
    public LoopAnalysis.LoopInfo getLoopInfo() {
        return cachedLoopInfo;
    }

    /** Set by {@link LoopAnalysis#analyze(CFG)}. Cleared by {@link #rebuildCFG()}. */
    void setLoopInfo(LoopAnalysis.LoopInfo info) {
        this.cachedLoopInfo = info;
    }

    /**
     * Validates flat Tiger-IR + CFG shape after {@link #rebuildCFG()} (e.g. end of
     * {@link SSABuilder#leavingSSA(CFG, boolean)} with {@code debug=true}).
     * Branch label resolution uses {@link #labelToBlock} as the canonical label→block map.
     */
    public void assertFlatInvariants() {
        if (basicBlocks.isEmpty()) {
            return;
        }
        BasicBlock entry = basicBlocks.get(0);
        List<IRInstruction> prog = function.getInstructions();

        for (BasicBlock bb : basicBlocks) {
            List<IRInstruction> ins = new ArrayList<>(bb.getInstructions());
            if (ins.isEmpty()) {
                throw new IllegalStateException(
                        "assertFlatInvariants: empty basic block [" + bb.getStartLine() + ".." + bb.getEndLine()
                                + "] in function " + function.name);
            }
        }

        for (BasicBlock bb : basicBlocks) {
            if (bb != entry && bb.getPredecessors().isEmpty()) {
                throw new IllegalStateException(
                        "assertFlatInvariants: non-entry block [" + bb.getStartLine() + ".." + bb.getEndLine()
                                + "] has no predecessors in function " + function.name);
            }
        }

        for (IRInstruction inst : prog) {
            switch (inst.opCode) {
                case GOTO:
                case BREQ:
                case BRNEQ:
                case BRLT:
                case BRGT:
                case BRLEQ:
                case BRGEQ: {
                    String lab = ((IRLabelOperand) inst.operands[0]).getName();
                    if (!labelToBlock.containsKey(lab)) {
                        throw new IllegalStateException(
                                "assertFlatInvariants: branch/goto to undefined label '" + lab + "' in function "
                                        + function.name);
                    }
                    break;
                }
                default:
                    break;
            }
        }

        for (IRInstruction inst : prog) {
            for (IROperand op : inst.operands) {
                if (op instanceof IRVariableOperand) {
                    String n = ((IRVariableOperand) op).getName();
                    if (n.indexOf('#') >= 0) {
                        throw new IllegalStateException(
                                "assertFlatInvariants: variable '" + n + "' still contains '#' in function "
                                        + function.name + " at " + inst);
                    }
                }
            }
        }
    }

    void dumpCFG()
    {
        int cnt = 0;
        System.err.println("CFG for function " + function.name);
        for (BasicBlock bb : basicBlocks) {
            System.err.println("Basic Block " + cnt + ": " + bb.getStartLine() + " - " + bb.getEndLine());
            System.err.println("    Successors: ");
            for (BasicBlock succ : bb.getSuccessors()) {
                System.err.println("        " + succ.getStartLine() + " - " + succ.getEndLine());
            }
            System.err.println("    Predecessors: ");
            for (BasicBlock pred : bb.getPredecessors()) {
                System.err.println("        " + pred.getStartLine() + " - " + pred.getEndLine());
            }
            cnt++;
        }
    }

}
