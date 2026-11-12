module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.CoherentVertices

/-!
# coherent nerve の零単体と dg 対象

概要：全ての coherent 零単体はその唯一の対象の標準頂点に等しい。
方針：零単体の native な頂点が一つだけであり、そのループの Hom 写像が単位で決まることを使う。
規約：零単体の全射性だけでなく厳密な同値を構成する。
使われ方：HA 1.3.1.17、Kerodon 2.5.9（Tag 00SC） の任意の端点から標準の pinched Hom への帰着。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open CategoryTheory CategoryTheory.SimplicialThickening DifferentialGraded
open scoped _root_.Simplicial
variable {R : Type u} [CommRing R] {D : Type v} [DGCategory R D]

/-- 概要：coherent 零単体は唯一の対象から標準頂点として再構成できる。
方針：対象を一意の頂点へ戻し、全てのループ単体を豊穣単位と同定する。
規約：Hom 写像の等式まで証明し、対象の一致だけで終えない。
使われ方：Kerodon 2.5.9（Tag 00SC） の固定した標準端点による充満忠実性の判定。 -/
lemma coherentVertex_reconstruct
    (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.doldKanCoherentNerve (R := R) (D := D)) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentVertex (R := R) (D := D) (s.obj (.mk (ULift.up 0))) = s := by
  have hX : ∀ X : SimplicialThickening (ULift.{u} (Fin 1)), X = .mk (ULift.up 0) := by
    rintro ⟨⟨i⟩⟩
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    rfl
  have ho : ∀ X, (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentVertex (R := R) (D := D) (s.obj (.mk (ULift.up 0)))).obj X = s.obj X := by
    intro X
    rw [hX X]
    rfl
  refine EnrichedFunctor.ext SSet ho ?_
  intro X Y
  rw [hX X, hX Y]
  simp only [eqToHom_refl, Category.comp_id]
  apply CategoryTheory.NatTrans.ext
  funext m
  apply ConcreteCategory.hom_ext
  intro p
  have hp : p = (eId SSet (SimplicialThickening.mk (ULift.up (0 : Fin 1)))).app m PUnit.unit :=
    CategoryTheory.Functor.ext (fun t ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathLoop_eq_id _ (p.obj t))
  have hs : (s.map (.mk (ULift.up 0)) (.mk (ULift.up 0))).app m
      ((eId SSet (SimplicialThickening.mk (ULift.up (0 : Fin 1)))).app m PUnit.unit) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardUnit (R := R) (D := D) (s.obj (.mk (ULift.up 0))) m.unop.len := by
    exact congrArg (fun φ : MonoidalCategory.tensorUnit SSet ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomSpace (R := R) (D := D) (s.obj (.mk (ULift.up 0)))
        (s.obj (.mk (ULift.up 0))) ↦ φ.app m PUnit.unit) (s.map_id (.mk (ULift.up 0)))
  change _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardUnit (R := R) (D := D) (s.obj (.mk (ULift.up 0))) m.unop.len =
    (s.map (.mk (ULift.up 0)) (.mk (ULift.up 0))).app m p
  rw [hp]
  exact hs.symm

/-- 概要：coherent nerve の零単体は元の dg 圏の対象と同値である。
方針：唯一の頂点で評価し、定値の標準頂点を逆写像とする。
規約：対象と係数環の宇宙に大小関係を仮定しない。
使われ方：HA 1.3.1.17 の写像空間の全端点への比較の移送。 -/
def coherentVertexEquiv : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.doldKanCoherentNerve (R := R) (D := D)) _⦋0⦌ ≃ D where
  toFun s := s.obj (.mk (ULift.up 0))
  invFun := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentVertex
  left_inv := coherentVertex_reconstruct
  right_inv _ := rfl

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
