"""Reviewed examples and independent LZ4 sequence certificates (no oracle decoder)."""
def literal(data, extra=None):
    if extra is None:
        extra = [] if len(data) < 15 else [len(data)-15]
    return dict(token=min(15,len(data))*16, literal_extension=extra,
                literals=list(data), offset=0, match_extension=[], match_length=0)

def match(data, offset, length):
    return dict(token=min(15,len(data))*16+min(15,length-4),
                literal_extension=[] if len(data)<15 else [len(data)-15],
                literals=list(data), offset=offset,
                match_extension=[] if length<19 else [length-19], match_length=length)

def encoded(ps):
    out = []
    for i,p in enumerate(ps):
        out += [p['token']] + p['literal_extension'] + p['literals']
        if i != len(ps)-1:
            out += [p['offset']%256,p['offset']//256] + p['match_extension']
    return out

def decoded(ps):
    out = []
    for i,p in enumerate(ps):
        out += p['literals']
        if i != len(ps)-1:
            for _ in range(p['match_length']):
                out.append(out[-p['offset']])
    return out

CASES = []
def good(name, ps, cap, end_ok=True):
    CASES.append(dict(name=name, input=encoded(ps), cap=cap, expected=decoded(ps),
                      result=len(decoded(ps)), pieces=ps, end_ok=end_ok))
def bad(name, data, cap):
    CASES.append(dict(name=name,input=data,cap=cap,expected=None,result=-1,pieces=None))

bad('empty_input', [], 0)
good('empty_block', [literal([])], 0)
good('one_literal', [literal([65])], 1)
good('slow_overlap', [match([65],1,7),literal(range(66,71))], 13)
good('hot_overlap', [match([65],1,7),literal(range(66,80))], 64)
good('hot_snapshot18', [match(range(65,69),4,4),literal(range(70,84))], 64)
good('slow_snapshot32', [match(range(65,84),19,19),literal(range(90,95))], 100)
good('slow_snapshot64', [match(range(65,98),33,33),literal(range(100,105))], 110)
good('extended_literals', [literal(range(65,81))], 16)
good('relaxed_end', [match([65],1,4),literal([])], 5, False)
bad('zero_offset', [0x10,65,0,0,0x50,66,67,68,69,70],32)
bad('offset_beyond_prefix', [0,1,0],64)
bad('truncated_literal', [0x20,65],32)
bad('truncated_extension', [0xf0,255],32)
bad('truncated_offset', [0x10,65,1],64)
bad('output_too_small', [0x10,65],0)
