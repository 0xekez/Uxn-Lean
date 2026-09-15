import Uxn.Uxn

namespace Uxn.Host.Port

-- Named byte addresses. match_pattern also permits their use in dispatch patterns.

namespace System
@[match_pattern] def state : Byte := 0x0f
end System

namespace Console
@[match_pattern] def vector : Byte := 0x10
@[match_pattern] def vectorLow : Byte := vector + 1
@[match_pattern] def read : Byte := 0x12
@[match_pattern] def type : Byte := 0x17
@[match_pattern] def write : Byte := 0x18
@[match_pattern] def error : Byte := 0x19
end Console

namespace File
@[match_pattern] def success : Byte := 0xa2
@[match_pattern] def name : Byte := 0xa8
@[match_pattern] def nameLow : Byte := name + 1
@[match_pattern] def length : Byte := 0xaa
@[match_pattern] def lengthLow : Byte := length + 1
@[match_pattern] def read : Byte := 0xac
@[match_pattern] def readLow : Byte := read + 1
end File

end Uxn.Host.Port
