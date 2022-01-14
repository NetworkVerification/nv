#!/usr/bin/env python3
from dataclasses import dataclass
from enum import Enum, IntEnum
import re
from typing import Optional


@dataclass
class Bgp:
    """A simplified version of the BGP attribute."""

    # 32-bit int
    aslen: int | str
    # set of 32-bit ints
    comms: set[int] = set()
    # 8-bit int
    bgpAd: int = 20
    # 32-bit int
    lp: int = 100
    # 32-bit int
    med: int = 80

    def __str__(self):
        aslen = f"{self.aslen}u32" if isinstance(self.aslen, int) else self.aslen
        comms = "{ " + "; ".join(map(str, self.comms)) + "_ |-> false" + " }"
        return f"{{  aslen= {aslen}; bgpAd= {self.bgpAd}u8; comms= {comms}; lp= {self.lp}u32; med= {self.med}u32; }}"

    @staticmethod
    def TypeDeclaration() -> str:
        return "type bgpType = {aslen: int; bgpAd: int8; comms: set[int]; lp: int; med: int;}"


@dataclass
class Rib:
    """A simplified version of the RIB attribute."""

    bgp: Optional[Bgp] = None
    static: Optional[int] = None
    selected: Optional[int] = None

    def select(self):
        # determine the selected attribute
        if self.static:
            self.selected = 1
        elif self.bgp:
            self.selected = 3
        else:
            self.selected = None
        return self

    def __str__(self):
        sel = "None" if self.selected is None else f"Some {self.selected}u2"
        static = "None" if self.static is None else f"Some {self.static}u8"
        bgp = "None" if self.bgp is None else f"Some {self.bgp}"
        return f"{{  bgp= {bgp}; connected= None; ospf= None; selected= {sel}; static= {static}; }}"

    @staticmethod
    def TypeDeclaration() -> str:
        return "type rib = {\n  connected:option[int8]\n  static:option[int8];\n  ospf:option[ospfType];\n  bgp:option[bgpType];\n  selected:option[int2]; }"


class AttrType(Enum):
    """Control which type of attribute the file uses."""

    INT_OPTION = 0
    RIB = 1
    BGP = 2

    @staticmethod
    def parse_from_file(text):
        pat = re.compile(r"type attribute = (.*)")
        m = pat.search(text)
        if m:
            match m.group(1):
                case "option[int]" | "option[int32]":
                    return AttrType.INT_OPTION
                case "rib":
                    return AttrType.RIB
                case "option[bgpType]":
                    return AttrType.BGP
                case _:
                    raise ValueError(
                        f"Couldn't determine attribute type from file contents: found {m.group(1)}"
                    )
        else:
            raise ValueError("Couldn't find attribute declaration in NV file.")


class NetType(Enum):
    SP = 0
    FATPOL = 1
    MAINTENANCE = 2
    RAND = 3
    OTHER = 4

    def is_fattree(self):
        """Return True if the network is a fattree network (SP, FATPOL or MAINTENANCE)."""
        match self:
            case NetType.SP | NetType.FATPOL | NetType.MAINTENANCE:
                return True
            case _:
                return False

    @staticmethod
    def from_filename(fname):
        if re.match(r"sp\d*", fname):
            return NetType.SP
        elif re.match(r"fat\d*Pol", fname):
            return NetType.FATPOL
        elif re.match(r"rand_\d*_\d*", fname):
            return NetType.RAND
        elif re.match(r"maintenance\d*", fname) or re.match(
            r"fat\d*Maintenance", fname
        ):
            return NetType.MAINTENANCE
        else:
            return NetType.OTHER


class NodeGroup(IntEnum):
    """
    Core nodes are on the spine, edge nodes are ToR,
    and aggregation nodes are between core and edge nodes.
    None is used when nodes are not in fattree networks.
    """

    CORE = 0
    AGGREGATION = 1
    EDGE = 2
    NONE = 3

    @staticmethod
    def parse(name):
        if name == "core":
            return NodeGroup.CORE
        elif name == "aggregation":
            return NodeGroup.AGGREGATION
        elif name == "edge":
            return NodeGroup.EDGE
        else:
            return NodeGroup.NONE


class FattreeCut(Enum):
    VERTICAL = ("v", "vertical")
    HORIZONTAL = ("h", "horizontal")
    PODS = ("p", "pods")
    SPINES = ("s", "spines")
    FULL = ("f", "full")

    def __init__(self, short: str, long: str):
        self.short = short
        self.long = long

    @property
    def desc(self):
        # description
        match self:
            case FattreeCut.VERTICAL:
                return "Vertically partitioned"
            case FattreeCut.HORIZONTAL:
                return "Horizontally partitioned"
            case FattreeCut.PODS:
                return "Partitioned into pods"
            case FattreeCut.SPINES:
                return "Partitioned into pods and individual spines"
            case FattreeCut.FULL:
                return "Fully partitioned"

    @staticmethod
    def as_list() -> list[str]:
        return [s for c in list(FattreeCut) for s in [c.short, c.long]]

    @staticmethod
    def from_str(s):
        for e in list(FattreeCut):
            if s == e.short or s == e.long:
                return e
        raise KeyError("cut not found")
