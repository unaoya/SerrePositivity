module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias
public import SerrePositivity.InfinityCategories.Kan.SimplicialEqualityTransport

/-! # 四辺と共通対角辺を保つ同じ二つの実二単体の移送
概要：元の二つの二単体全体を同じ単体集合へ移し、全四辺と共通対角辺を厳密に回収する。
方針：単体集合の表示等号で同じ二単体を写し、四面の依存等号と共通面の等号を移す。
規約：新しい二単体を充填・選択しない。元の全二単体の像を証拠として保存する。
使われ方：三入力 BF 比較の四辺の照合を同じ実二次元比較データへ束ねる。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
end SerrePositivity.KST.SConstruction
namespace SerrePositivity.InfinityCategories.Kan
open SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open scoped _root_.Simplicial

/-- 全四辺と同じ対角辺を保持する、同じ単体集合内の二つの実二単体。 -/
structure TriangleDiamondData (E : SSet.{u})
    (firstLower secondLower firstUpper secondUpper : E _⦋1⦌) where
  /-- 第一経路の全二単体。 -/
  first : E _⦋2⦌
  /-- 第二経路の全二単体。 -/
  second : E _⦋2⦌
  /-- 第一経路の元の下辺。 -/
  first_lower : E.δ 2 _root_.SerrePositivity.InfinityCategories.Kan.TriangleDiamondData.first = firstLower
  /-- 第二経路の元の下辺。 -/
  second_lower : E.δ 2 _root_.SerrePositivity.InfinityCategories.Kan.TriangleDiamondData.second = secondLower
  /-- 第一経路の元の上辺。 -/
  first_upper : E.δ 0 _root_.SerrePositivity.InfinityCategories.Kan.TriangleDiamondData.first = firstUpper
  /-- 第二経路の元の上辺。 -/
  second_upper : E.δ 0 _root_.SerrePositivity.InfinityCategories.Kan.TriangleDiamondData.second = secondUpper
  /-- 全二単体が共有する同じ実対角辺。 -/
  diagonal : E.δ 1 _root_.SerrePositivity.InfinityCategories.Kan.TriangleDiamondData.first = E.δ 1 _root_.SerrePositivity.InfinityCategories.Kan.TriangleDiamondData.second

/-- 元の二単体の全像を証拠として保存し、全四辺と共通対角辺を同時に回収する。 -/
def triangleDiamondTransportData {E D : SSet.{u}} (e : E = D) (s t : E _⦋2⦌)
    (firstLower secondLower firstUpper secondUpper : D _⦋1⦌)
    (hfl : HEq (E.δ 2 s) firstLower) (hsl : HEq (E.δ 2 t) secondLower)
    (hfu : HEq (E.δ 0 s) firstUpper) (hsu : HEq (E.δ 0 t) secondUpper)
    (hd : E.δ 1 s = E.δ 1 t) :
    {T : _root_.SerrePositivity.InfinityCategories.Kan.TriangleDiamondData D firstLower secondLower firstUpper secondUpper //
      T.first = (eqToHom e).app (Opposite.op ⦋2⦌) s ∧
      T.second = (eqToHom e).app (Opposite.op ⦋2⦌) t} :=
  ⟨{ _root_.SerrePositivity.InfinityCategories.Kan.TriangleDiamondData.first := (eqToHom e).app (Opposite.op ⦋2⦌) s
     _root_.SerrePositivity.InfinityCategories.Kan.TriangleDiamondData.second := (eqToHom e).app (Opposite.op ⦋2⦌) t
     _root_.SerrePositivity.InfinityCategories.Kan.TriangleDiamondData.first_lower := _root_.SerrePositivity.InfinityCategories.Kan.simplicialEqualityTransport_face_of_heq e 2 s firstLower hfl
     _root_.SerrePositivity.InfinityCategories.Kan.TriangleDiamondData.second_lower := _root_.SerrePositivity.InfinityCategories.Kan.simplicialEqualityTransport_face_of_heq e 2 t secondLower hsl
     _root_.SerrePositivity.InfinityCategories.Kan.TriangleDiamondData.first_upper := _root_.SerrePositivity.InfinityCategories.Kan.simplicialEqualityTransport_face_of_heq e 0 s firstUpper hfu
     _root_.SerrePositivity.InfinityCategories.Kan.TriangleDiamondData.second_upper := _root_.SerrePositivity.InfinityCategories.Kan.simplicialEqualityTransport_face_of_heq e 0 t secondUpper hsu
     _root_.SerrePositivity.InfinityCategories.Kan.TriangleDiamondData.diagonal := _root_.SerrePositivity.InfinityCategories.Kan.simplicialEqualityTransport_common_face e 1 s t hd }, rfl, rfl⟩

end SerrePositivity.InfinityCategories.Kan

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.TriangleDiamondData (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.TriangleDiamondData := _root_.SerrePositivity.InfinityCategories.Kan.TriangleDiamondData

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.triangleDiamondTransportData (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.triangleDiamondTransportData := _root_.SerrePositivity.InfinityCategories.Kan.triangleDiamondTransportData

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.TriangleDiamondData._sizeOf_1 (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.SConstruction.TriangleDiamondData._sizeOf_1 := _root_.SerrePositivity.InfinityCategories.Kan.TriangleDiamondData._sizeOf_1

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.TriangleDiamondData._sizeOf_inst (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.SConstruction.TriangleDiamondData._sizeOf_inst := _root_.SerrePositivity.InfinityCategories.Kan.TriangleDiamondData._sizeOf_inst

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.TriangleDiamondData.casesOn (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.TriangleDiamondData.casesOn := _root_.SerrePositivity.InfinityCategories.Kan.TriangleDiamondData.casesOn

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.TriangleDiamondData.ctorIdx (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.TriangleDiamondData.ctorIdx := _root_.SerrePositivity.InfinityCategories.Kan.TriangleDiamondData.ctorIdx

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.TriangleDiamondData.diagonal := _root_.SerrePositivity.InfinityCategories.Kan.TriangleDiamondData.diagonal

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.TriangleDiamondData.first (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.TriangleDiamondData.first := _root_.SerrePositivity.InfinityCategories.Kan.TriangleDiamondData.first

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.TriangleDiamondData.first_lower := _root_.SerrePositivity.InfinityCategories.Kan.TriangleDiamondData.first_lower

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.TriangleDiamondData.first_upper := _root_.SerrePositivity.InfinityCategories.Kan.TriangleDiamondData.first_upper

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.TriangleDiamondData.mk (since := "2026-11-05"), match_pattern]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.TriangleDiamondData.mk := _root_.SerrePositivity.InfinityCategories.Kan.TriangleDiamondData.mk

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.TriangleDiamondData.noConfusion (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.SConstruction.TriangleDiamondData.noConfusion := _root_.SerrePositivity.InfinityCategories.Kan.TriangleDiamondData.noConfusion

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.TriangleDiamondData.noConfusionType (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.TriangleDiamondData.noConfusionType := _root_.SerrePositivity.InfinityCategories.Kan.TriangleDiamondData.noConfusionType

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.TriangleDiamondData.rec (since := "2026-11-05"), elab_as_elim]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.TriangleDiamondData.rec := _root_.SerrePositivity.InfinityCategories.Kan.TriangleDiamondData.rec

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.TriangleDiamondData.recOn (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.SConstruction.TriangleDiamondData.recOn := _root_.SerrePositivity.InfinityCategories.Kan.TriangleDiamondData.recOn

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.TriangleDiamondData.second (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.TriangleDiamondData.second := _root_.SerrePositivity.InfinityCategories.Kan.TriangleDiamondData.second

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.TriangleDiamondData.second_lower := _root_.SerrePositivity.InfinityCategories.Kan.TriangleDiamondData.second_lower

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.TriangleDiamondData.second_upper := _root_.SerrePositivity.InfinityCategories.Kan.TriangleDiamondData.second_upper

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.triangleDiamondTransportData._proof_1 := _root_.SerrePositivity.InfinityCategories.Kan.triangleDiamondTransportData._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.triangleDiamondTransportData._proof_2 := _root_.SerrePositivity.InfinityCategories.Kan.triangleDiamondTransportData._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.triangleDiamondTransportData._proof_3 := _root_.SerrePositivity.InfinityCategories.Kan.triangleDiamondTransportData._proof_3

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.triangleDiamondTransportData._proof_4 := _root_.SerrePositivity.InfinityCategories.Kan.triangleDiamondTransportData._proof_4

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.triangleDiamondTransportData._proof_5 := _root_.SerrePositivity.InfinityCategories.Kan.triangleDiamondTransportData._proof_5

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.TriangleDiamondData.mk._flat_ctor (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.SConstruction.TriangleDiamondData.mk._flat_ctor := _root_.SerrePositivity.InfinityCategories.Kan.TriangleDiamondData.mk._flat_ctor

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.TriangleDiamondData.mk.inj := _root_.SerrePositivity.InfinityCategories.Kan.TriangleDiamondData.mk.inj

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.TriangleDiamondData.mk.injEq := _root_.SerrePositivity.InfinityCategories.Kan.TriangleDiamondData.mk.injEq

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.TriangleDiamondData.mk.noConfusion (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.SConstruction.TriangleDiamondData.mk.noConfusion := _root_.SerrePositivity.InfinityCategories.Kan.TriangleDiamondData.mk.noConfusion

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.TriangleDiamondData.mk.sizeOf_spec := _root_.SerrePositivity.InfinityCategories.Kan.TriangleDiamondData.mk.sizeOf_spec
