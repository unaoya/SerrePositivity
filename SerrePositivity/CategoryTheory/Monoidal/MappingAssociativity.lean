module

public import SerrePositivity.CategoryTheory.Monoidal.MappingUnitLaws

/-! # 作用の五角形から得る写像対象の合成の結合性 -/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace SerrePositivity.MappingAssociativity

open CategoryTheory CategoryTheory.MonoidalCategory

variable {V : Type u₁} {D : Type u₂} [Category.{v₁} V] [Category.{v₂} D]
  [MonoidalCategory V] (H : V ⥤ D ⥤ D)
  (a : ∀ P Q : V, H.obj (P ⊗ Q) ≅ H.obj Q ⋙ H.obj P)

/-- 結同比較を通り、二つの評価を適用する射。 -/
def compositionEvaluation (P Q : V) {E F G : D}
    (v : (H.obj Q).obj E ⟶ F) (w : (H.obj P).obj F ⟶ G) :
    (H.obj (P ⊗ Q)).obj E ⟶ G :=
  (a P Q).hom.app E ≫ (H.obj P).map v ≫ w

/-- 二通りの反復合成を評価した射が等しいという法則。 -/
def associativityEvaluationLaw {P Q R S T : V} {E F G K : D}
    (m : P ⊗ Q ⟶ S) (n : Q ⊗ R ⟶ T)
    (v : (H.obj R).obj E ⟶ F)
    (z : (H.obj P).obj G ⟶ K) (s : (H.obj S).obj F ⟶ K)
    (t : (H.obj T).obj E ⟶ G) : Prop :=
  (H.map (m ⊗ₘ 𝟙 R)).app E ≫ compositionEvaluation H a S R v s =
    (H.map ((α_ P Q R).hom ≫ (𝟙 P ⊗ₘ n))).app E ≫
      compositionEvaluation H a P T t z

/-- 結同比較の自然性と五角形により、反復合成の評価は一致する。 -/
lemma associativity_evaluation {P Q R S T : V} {E F G K : D}
    (m : P ⊗ Q ⟶ S) (n : Q ⊗ R ⟶ T)
    (v : (H.obj R).obj E ⟶ F) (w : (H.obj Q).obj F ⟶ G)
    (z : (H.obj P).obj G ⟶ K) (s : (H.obj S).obj F ⟶ K)
    (t : (H.obj T).obj E ⟶ G)
    (hm : (H.map m).app F ≫ s = compositionEvaluation H a P Q w z)
    (hn : (H.map n).app E ≫ t = compositionEvaluation H a Q R v w)
    (hl : (H.map (m ⊗ₘ 𝟙 R)).app E ≫ (a S R).hom.app E =
      (a (P ⊗ Q) R).hom.app E ≫ (H.map m).app ((H.obj R).obj E))
    (hr : (H.map (𝟙 P ⊗ₘ n)).app E ≫ (a P T).hom.app E =
      (a P (Q ⊗ R)).hom.app E ≫ (H.obj P).map ((H.map n).app E))
    (hp : (H.map (α_ P Q R).hom).app E ≫ (a P (Q ⊗ R)).hom.app E ≫
      (H.obj P).map ((a Q R).hom.app E) =
        (a (P ⊗ Q) R).hom.app E ≫ (a P Q).hom.app ((H.obj R).obj E)) :
    associativityEvaluationLaw H a m n v z s t := by
  unfold associativityEvaluationLaw compositionEvaluation at *
  rw [H.map_comp, NatTrans.comp_app]
  rw [reassoc_of% hl, ← reassoc_of% ((H.map m).naturality v), hm]
  simp only [Category.assoc]
  rw [reassoc_of% ((a P Q).hom.naturality v)]
  rw [reassoc_of% hr]
  conv_rhs => rw [← CategoryTheory.Functor.map_comp_assoc, hn]
  rw [(H.obj P).map_comp, (H.obj P).map_comp]
  simp only [Category.assoc]
  rw [← reassoc_of% hp]

/-- 評価の一致を転置して得る写像対象の結合則の等式。 -/
def representedAssociativityLaw {E F G K : D} {U : D ⥤ V}
    (adj : MappingUnitLaws.parameterFunctor H E ⊣ U)
    {P Q R S T : V} (m : P ⊗ Q ⟶ S) (n : Q ⊗ R ⟶ T)
    (v : (H.obj R).obj E ⟶ F) (z : (H.obj P).obj G ⟶ K)
    (s : (H.obj S).obj F ⟶ K) (t : (H.obj T).obj E ⟶ G) : Prop :=
  AdjunctionHomLaws.curryPreComparisonLaw adj
    (compositionEvaluation H a S R v s) (compositionEvaluation H a P T t z)
    (m ⊗ₘ 𝟙 R) ((α_ P Q R).hom ≫ (𝟙 P ⊗ₘ n))

/-- 表現性と反復合成の評価の一致から、写像対象の結合則を得る。 -/
lemma represented_associativity {E F G K : D} {U : D ⥤ V}
    (adj : MappingUnitLaws.parameterFunctor H E ⊣ U)
    {P Q R S T : V} (m : P ⊗ Q ⟶ S) (n : Q ⊗ R ⟶ T)
    (v : (H.obj R).obj E ⟶ F) (z : (H.obj P).obj G ⟶ K)
    (s : (H.obj S).obj F ⟶ K) (t : (H.obj T).obj E ⟶ G)
    (h : associativityEvaluationLaw H a m n v z s t) :
    representedAssociativityLaw H a adj m n v z s t :=
  AdjunctionHomLaws.curry_pre_comparison_of_evaluation adj
    (compositionEvaluation H a S R v s) (compositionEvaluation H a P T t z)
    (m ⊗ₘ 𝟙 R) ((α_ P Q R).hom ≫ (𝟙 P ⊗ₘ n)) h

end SerrePositivity.MappingAssociativity
