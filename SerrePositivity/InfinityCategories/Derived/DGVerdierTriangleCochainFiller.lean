module
public import SerrePositivity.InfinityCategories.Derived.DGFourLastHornSolution
public import SerrePositivity.InfinityCategories.Derived.DGVerdierDiagramTriangleFiller

/-! # 四次ホーンの二未知 cochain の解から実図式の三次整合性へ

概要：実二単体と三辺錐から回収した Q・A の解を、実分母部分圏の三単体へ戻す。
方針：型付き解の実ホーン延長を、指定四面を保つ回収へ接続する。
規約：解の存在は仮定として明示。使われ方：追加閉細分後の代数的解の受入。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]
variable {P : Set D} {x : D} {K : SSet.{max u v}}
variable {f : K ⟶ (dgVerdierOver A D P x : SSet.{max u v})}
variable (C : DGVerdierDiagramVertexCone A D P x f) (σ : K _⦋2⦌)
variable (H : ∀ i : Fin 3, Truncated.Edge.CompStruct
  (C.leg (K.δ 1 (K.δ i σ)))
  ((edgeOfSimplex (K.δ i σ)).map ((truncation 2).map f))
  (C.leg (K.δ 0 (K.δ i σ))))
variable (S : DGFourLastHornSolution (dgVerdierDiagramTriangleHorn A D C σ H))

/-- 実四次ホーンの Q・A の解は、実分母部分圏の三次整合性を与える。 -/
def dgVerdierDiagramTriangleFillerOfCochains : (dgVerdierOver A D P x : SSet) _⦋3⦌ :=
  dgVerdierDiagramTriangleFiller A D C σ H S.extension S.fac

/-- 解から回収した三単体は、元の実図式二単体を零面に保つ。 -/
lemma dgVerdierDiagramTriangleFillerOfCochains_face0 :
    (dgVerdierOver A D P x : SSet).δ 0
      (dgVerdierDiagramTriangleFillerOfCochains A D C σ H S) = f.app _ σ :=
  dgVerdierDiagramTriangleFiller_face0 A D C σ H S.extension S.fac

/-- 解から回収した三単体は、元の指定三辺錐を全て厳密に保つ。 -/
lemma dgVerdierDiagramTriangleFillerOfCochains_face_cone (i : Fin 3) :
    (dgVerdierOver A D P x : SSet).δ i.succ
      (dgVerdierDiagramTriangleFillerOfCochains A D C σ H S) = (H i).simplex :=
  dgVerdierDiagramTriangleFiller_face_cone A D C σ H S.extension S.fac i

end SerrePositivity.InfinityCategories
