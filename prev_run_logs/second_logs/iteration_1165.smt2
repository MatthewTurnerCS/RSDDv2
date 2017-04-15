; playing with this smt to try and figure out why mathsat5 and z3 generate
; different answers!

; original:
; (declare-fun f0 (Float64 Float128 Float64) Float64)
; (declare-fun p0 (Float128 Float128) Bool)
; ; GENERATING VARIABLES
; (declare-const ?float2 Float64)
; (declare-const ?float3 Float16)
; ; GENERATING CONSTS
; (declare-const ?float4 Float64)
; (assert (= ?float4 (fp #b1 #b00000000001 #b0000000000000000000000000000000000000000000000000000)))
; (declare-const ?float5 Float16)
; (assert (= ?float5 (fp #b0 #b00000 #b0000000000)))
; ; DERIVE FLOATS
; (declare-const ?float6 Float64)
; (assert (= ?float6 (fp.div RNE ?float4 ((_ to_fp 11 53) RTP ?float5))))
; (declare-const ?float7 Float16)
; (assert (= ?float7 (fp.max ?float3 ?float5)))
; (declare-const ?float8 Float64)
; (assert (= ?float8 (f0 ?float6 ((_ to_fp 15 113) RTN ?float2) ?float2)))
; (declare-const ?float9 Float16)
; (assert (= ?float9 (fp.max ?float7 ?float3)))
; (declare-const ?float10 Float64)
; (assert (= ?float10 (fp.div RTN ?float6 ?float2)))
; ; DERIVE BOOLS
; (declare-const ?bool11 Bool)
; (assert (= ?bool11 (fp.geq ?float3 ?float3)))
; (declare-const ?bool12 Bool)
; (assert (= ?bool12 (fp.isInfinite ?float6)))
; (declare-const ?bool13 Bool)
; (assert (= ?bool13 (fp.isNegative ?float7)))
; (declare-const ?bool14 Bool)
; (assert (= ?bool14 (fp.lt ?float4 ?float10)))
; (declare-const ?bool15 Bool)
; (assert (= ?bool15 (fp.isNegative ?float6)))
; ; FINAL ASSERT
; (assert (and ?bool11 ?bool13))
; (check-sat)

(declare-fun f0 (Float64 Float128 Float64) Float64)
(declare-fun p0 (Float128 Float128) Bool)
; GENERATING VARIABLES
(declare-const ?float2 Float64)
(declare-const ?float3 Float16)
; GENERATING CONSTS
(declare-const ?float4 Float64)
(assert (= ?float4 (fp #b1 #b00000000001 #b0000000000000000000000000000000000000000000000000000)))
(declare-const ?float5 Float16)
(assert (= ?float5 (fp #b0 #b00000 #b0000000000)))
; DERIVE FLOATS
(declare-const ?float6 Float64)
(assert (= ?float6 (fp.div RNE ?float4 ((_ to_fp 11 53) RTP ?float5))))
(declare-const ?float7 Float16)
(assert (= ?float7 (fp.max ?float3 ?float5)))
(declare-const ?float8 Float64)
(assert (= ?float8 (f0 ?float6 ((_ to_fp 15 113) RTN ?float2) ?float2)))
(declare-const ?float9 Float16)
(assert (= ?float9 (fp.max ?float7 ?float3)))
(declare-const ?float10 Float64)
(assert (= ?float10 (fp.div RTN ?float6 ?float2)))
; DERIVE BOOLS
(declare-const ?bool11 Bool)
(assert (= ?bool11 (fp.geq ?float3 ?float3)))
(declare-const ?bool12 Bool)
(assert (= ?bool12 (fp.isInfinite ?float6)))
(declare-const ?bool13 Bool)
(assert (= ?bool13 (fp.isNegative ?float7)))
(declare-const ?bool14 Bool)
(assert (= ?bool14 (fp.lt ?float4 ?float10)))
(declare-const ?bool15 Bool)
(assert (= ?bool15 (fp.isNegative ?float6)))
; FINAL ASSERT
(assert (and ?bool11 ?bool13))
(check-sat)

; distilled problem!
(declare-const ?float1 Float16)
(assert (fp.isPositive (fp.max ?float1 (fp #b0 #b00000 #b0000000000))))
(check-sat)
