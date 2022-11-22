#!/usr/bin/env python3
from dataclasses import dataclass
from enum import Enum, IntEnum
import re
from typing import Optional


class If:
    def __init__(self, condition, then_branch, else_branch):
        self.condition = condition
        self.then_branch = then_branch
        self.else_branch = else_branch

    def __str__(self) -> str:
        return f"if {self.condition} then {self.then_branch} else {self.else_branch}"


class Bgp:
    """A simplified version of the BGP attribute."""

    def __init__(
        self,
        aslen: int | str,
        comms: set[int] = set(),
        bgpAd: int = 20,
        lp: int = 100,
        med: int = 80,
    ):
        self.aslen = aslen
        self.comms = comms
        self.bgpAd = bgpAd
        self.lp = lp
        self.med = med

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
    static: Optional[int | str] = None
    selected: Optional[int | str] = None

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
        match self.selected:
            case None:
                sel = "None"
            case int() as v:
                sel = f"Some {v}u2"
            case str() as v:
                sel = v
            case _:
                raise Exception("Invalid self.selected type")
        match self.static:
            case None:
                static = "None"
            case int() as v:
                static = f"Some {v}u8"
            case str() as v:
                static = v
            case _:
                raise Exception("Invalid self.static type")
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
    FT = 3
    AP = 4
    APPOL = 5
    RAND = 6
    OTHER = 7

    def is_fattree(self):
        """Return True if the network is a fattree network (SP, FATPOL or MAINTENANCE)."""
        match self:
            case NetType.SP | NetType.FATPOL | NetType.MAINTENANCE | NetType.FT | NetType.AP | NetType.APPOL:
                return True
            case _:
                return False

    @staticmethod
    def from_filename(fname):
        if re.match(r"sp\d*", fname):
            return NetType.SP
        elif re.match(r"ap\d*", fname):
            return NetType.AP
        elif re.match(r"apFat\d*Pol", fname):
            return NetType.APPOL
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

    def community(self, pod: int, follow_up: bool) -> int:
        """
        Return the first BGP community tag associated with the node.
        If follow_up is true, this is the second tag that is added
        once the first is already present (see topoconfig.py).
        NOTE: the community tag is a standard community represented by a 32-bit integer,
        meaning the pod must be at most 65535.
        """
        if not (0 <= pod < 65536):
            raise ValueError("pod must be a number between [0,65535]")
        match self:
            case NodeGroup.CORE:
                asn = 6 if follow_up else 3
                tag = 0
            case NodeGroup.AGGREGATION:
                asn = 4 if follow_up else 1
                tag = pod
            case NodeGroup.EDGE:
                asn = 5 if follow_up else 2
                tag = pod
            case _:
                asn = 0
                tag = 0
        # the resulting community int is a 32-bit number, where the asn occupies the upper 16 bits
        # and the tag occupies the lower 16 bits
        # see https://github.com/batfish/batfish/blob/master/projects/batfish-common-protocol/src/main/java/org/batfish/datamodel/bgp/community/StandardCommunity.java
        return asn << 16 | tag


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
