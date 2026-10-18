module

public import SerrePositivity.KST.DerivedGeometry.LinearRepresentableCone
public import SerrePositivity.KST.DerivedGeometry.LinearConeTriangles

/-!
概要：代表加群の標準 cone 同型の評価を具体的な写像複体の同型と照合する。
方針：成分族の同一視による射を評価し、既に証明した cone 比較へ戻す。
規約：標準 cone の入力射の等式による輸送を明示する。
使われ方：Drinfeld §2.4、KST D4・§10-7 の標準三角形の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory CochainComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.DerivedGeometry.LinearComplex
variable (A : Type u) [CommRing A] {C : Type v} [Category.{u} C] [Preadditive C] [Linear A C]
attribute [local instance] enrichment
variable [Small.{u} (CochainComplex C ℤ)] [Limits.HasBinaryBiproducts C]

/--
概要：成分ごとの cone と元の cone の代表加群との同型を評価する。
方針：全次数自然な chain 同型から作った加群同型の評価公式を使う。
規約：評価は既に構成した同じ比較射となる。
使われ方：Drinfeld §2.4、KST D4 の三角形の比較。
-/
theorem representableConeIso_hom_eval {X Y : CochainComplex C ℤ} (f : X ⟶ Y)
    (T : CochainComplex C ℤ) :
    (moduleEvaluation A (CochainComplex C ℤ) T).map (representableConeIso A f).hom =
      mappingConeComparison A T f :=
  moduleIsoMk_hom_eval A (CochainComplex C ℤ) _ _ T

/--
概要：標準 cone の代表加群の同型を評価すると、同じ写像複体の cone 比較になる。
方針：入力射の評価の等式による輸送を残し、加群同型の各成分を計算する。
規約：等しい入力射の cone を定義上同じと仮定しない。
使われ方：Drinfeld §2.4、KST D4・§10-7 の標準三角形と局所化。
-/
theorem representableStandardConeIso_hom_eval {X Y : CochainComplex C ℤ} (f : X ⟶ Y)
    (T : CochainComplex C ℤ) :
    (moduleEvaluation A (CochainComplex C ℤ) T).map (representableStandardConeIso A f).hom =
      eqToHom (congrArg (fun g => mappingCone g) (representablePostcompose_eval A f T)) ≫
        mappingConeComparison A T f := by
  unfold representableStandardConeIso
  simp only [Iso.trans_hom, CategoryTheory.Functor.map_comp,
    eqToIso.hom, eqToHom_map]
  rw [representableConeIso_hom_eval]

end SerrePositivity.KST.DerivedGeometry.LinearComplex
