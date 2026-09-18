import ProgramProofs.Uxnmin.Semantics
import ProgramProofs.Host.Reduction
import ProgramProofs.Host.IO
import Mathlib.Tactic.Conv

set_option linter.unusedSimpArgs false
set_option maxRecDepth 30000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

namespace ProgramProofs.Uxnmin
open Uxn Uxn.Host ProgramProofs.Host

/-- One argument byte is copied to the filename buffer and advances its cursor. -/
theorem filename_byte (ram : Word → Byte) (hc : Code rom rom.size ram)
    (index byte : Byte) (w r : Byte → Byte) (host : Uxn.Host.State) (fuel : Nat)
    (input : host.read 0x12#8 = byte) (kind : host.read 0x17#8 = 2#8) :
    ∃ final : Uxn.Host.State,
      evalLoop (.next (machine (Function.update ram 0x13e index) 0x118 ⟨w, 0⟩ ⟨r, 0⟩))
        { host with fuel := some (fuel + 12) } = pure ((), final) ∧
      final.fuel = some fuel ∧ final.vm.pc = 0x145 ∧
      final.ports = host.ports ∧ final.consoleVector = host.consoleVector ∧ final.file = host.file ∧
      final.vm.mem.ram = Function.update (Function.update ram 0x13e (index + 1))
        (index.setWidth 16) byte ∧
      final.vm.mem.wstk.ptr = 0 ∧ final.vm.mem.rstk.ptr = 0 := by
  have low : 0x144#16 ≠ index.setWidth 16 := by bv_omega
  have read_eq (host : Uxn.Host.State) (port : Byte) :
      host.read port = host.ports[port.toNat] := rfl
  rw [read_eq] at input kind
  simp at input kind
  have h24 : ram 0x118#16 = 0xa0#8 := hc ⟨24, by decide⟩
  have h25 : ram 0x119#16 = 0x3#8 := hc ⟨25, by decide⟩
  have h26 : ram 0x11a#16 = 0x17#8 := hc ⟨26, by decide⟩
  have h27 : ram 0x11b#16 = 0x16#8 := hc ⟨27, by decide⟩
  have h28 : ram 0x11c#16 = 0xa#8 := hc ⟨28, by decide⟩
  have h29 : ram 0x11d#16 = 0x20#8 := hc ⟨29, by decide⟩
  have h30 : ram 0x11e#16 = 0x0#8 := hc ⟨30, by decide⟩
  have h31 : ram 0x11f#16 = 0x1a#8 := hc ⟨31, by decide⟩
  have h58 : ram 0x13a#16 = 0x80#8 := hc ⟨58, by decide⟩
  have h59 : ram 0x13b#16 = 0x12#8 := hc ⟨59, by decide⟩
  have h60 : ram 0x13c#16 = 0x16#8 := hc ⟨60, by decide⟩
  have h61 : ram 0x13d#16 = 0x80#8 := hc ⟨61, by decide⟩
  have h63 : ram 0x13f#16 = 0x81#8 := hc ⟨63, by decide⟩
  have h64 : ram 0x140#16 = 0x80#8 := hc ⟨64, by decide⟩
  have h65 : ram 0x141#16 = 0xfb#8 := hc ⟨65, by decide⟩
  have h66 : ram 0x142#16 = 0x13#8 := hc ⟨66, by decide⟩
  have h67 : ram 0x143#16 = 0x11#8 := hc ⟨67, by decide⟩
  have h68 : ram 0x144#16 = 0x0#8 := hc ⟨68, by decide⟩
  iterate 12
    rw [evalLoop.eq_def]
    simp [uxn_state, Uxn.Host.step]
    conv =>
      pattern Uxn.step _
      simp only [machine, Uxn.step, stepM, fetchInstruction, fetchByte,
        StateT.run, Bind.bind, StateT.bind, modifyGet, MonadStateOf.modifyGet,
        StateT.modifyGet, Pure.pure, StateT.pure]
      simp [h24, h25, h26, h27, h28, h29, h30, h31, h58, h59, h60, h61, h63, h64, h65, h66, h67, h68, Function.update_apply, low]
      dsimp [Uxn.Instruction.ofByte]
      simp [uxn_state, uxn_step, h24, h25, h26, h27, h28, h29, h30, h31, h58, h59, h60, h61, h63, h64, h65, h66, h67, h68, Function.update_apply, low, input, kind]
    try dsimp [Request.Result]
    simp [respond, uxn_state]
    try simp [uxn_state, read_eq, input, kind, Patch.apply, Function.update_apply,
      BitVec.sub_eq_add_neg, BitVec.add_assoc, Vector.getElem_set]
  rw [evalLoop.eq_def]
  simp only [uxn_state]
  refine ⟨_, rfl, ?_⟩
  have increment : (index.setWidth 16 + 1#16).setWidth 8 = index + 1#8 := by bv_omega
  simp [Function.update_comm, Function.update_idem, increment]

/-- Delivering one filename argument byte runs the verified native callback. -/
theorem console_filename_byte (ram : Word → Byte) (hc : Code rom rom.size ram)
    (index byte : Byte) (host : Uxn.Host.State) (fuel : Nat)
    (vector : host.consoleVector = 0x118)
    (memory : host.vm.mem.ram = Function.update ram 0x13e index)
    (working : host.vm.mem.wstk.ptr = 0) (returning : host.vm.mem.rstk.ptr = 0) :
    ∃ final : Uxn.Host.State,
      run.consoleInput byte 2 { host with fuel := some (fuel + 12) } = pure ((), final) ∧
      final.fuel = some fuel ∧ final.vm.pc = 0x145 ∧
      final.ports = ((host.write 0x12 byte).write 0x17 2).ports ∧
      final.consoleVector = 0x118 ∧ final.file = host.file ∧
      final.vm.mem.ram = Function.update (Function.update ram 0x13e (index + 1))
        (index.setWidth 16) byte ∧
      final.vm.mem.wstk.ptr = 0 ∧ final.vm.mem.rstk.ptr = 0 := by
  have read_eq (host : Uxn.Host.State) (port : Byte) :
      host.read port = host.ports[port.toNat] := rfl
  obtain ⟨final, executed, budget, pc, ports, callback, file, ram', wptr, rptr⟩ :=
    filename_byte ram hc index byte host.vm.mem.wstk.data host.vm.mem.rstk.data
      ((host.write 0x12 byte).write 0x17 2) fuel
      (by simp [read_eq, Host.State.write, Vector.getElem_set])
      (by simp [read_eq, Host.State.write, Vector.getElem_set])
  have machine_eq : { host.vm with pc := 0x118 } =
      machine (Function.update ram 0x13e index) 0x118
        ⟨host.vm.mem.wstk.data, 0⟩ ⟨host.vm.mem.rstk.data, 0⟩ := by
    cases hvm : host.vm with
    | mk pc mem =>
      cases mem with
      | mk ram w r =>
        cases w
        cases r
        simp_all [machine]
  refine ⟨final, ?_, budget, pc, ports, callback.trans vector, file, ram', wptr, rptr⟩
  unfold run.consoleInput eval
  simp only [uxn_state]
  simp only [BitVec.ofNat_eq_ofNat] at machine_eq
  simp [uxn_state, vector, Host.State.write, Port.Console.read, Port.Console.type] at executed ⊢
  rw [machine_eq]
  exact executed

end ProgramProofs.Uxnmin
