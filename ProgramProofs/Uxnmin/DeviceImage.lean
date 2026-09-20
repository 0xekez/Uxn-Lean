import ProgramProofs.Uxnmin.Representation

namespace ProgramProofs.Uxnmin
open Uxn Uxn.Host

/-- Ordinary ports use shadow RAM. Console input uses mutable literals; the
console vector is latched when its low-byte port is written. -/
structure DeviceImage (guest : Uxn.Host.State) (outer : Uxn.State) : Prop where
  ports : ∀ port : Byte, port ≠ Port.Console.read → port ≠ Port.Console.type →
    outer.mem.ram (0x759 + port.setWidth 16) = guest.read port
  consoleRead : outer.mem.ram 0x199 = guest.read Port.Console.read
  consoleType : outer.mem.ram 0x1a4 = guest.read Port.Console.type
  vector : outer.mem.ram 0x175 ++ outer.mem.ram 0x176 = guest.consoleVector

end ProgramProofs.Uxnmin
