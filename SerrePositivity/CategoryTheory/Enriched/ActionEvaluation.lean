module

public import Mathlib.CategoryTheory.Monoidal.Closed.Braided
public import Mathlib.CategoryTheory.Adjunction.Basic
public import SerrePositivity.CategoryTheory.Adjunction.Comparison
public import Mathlib.CategoryTheory.Monoidal.Category
public import Mathlib.CategoryTheory.Adjunction.Parametrized
public import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas
public import SerrePositivity.CategoryTheory.Enriched.BaseChange
public import Mathlib.CategoryTheory.Enriched.Ordinary.Basic

/-!
# 作用の結合・単位による評価の計算
-/

/-! # 作用の表現性から得る写像対象の左単位の評価 -/

@[expose] public section MappingUnitLaws
universe v₁ v₂ u₁ u₂

namespace SerrePositivity.MappingUnitLaws

open CategoryTheory CategoryTheory.MonoidalCategory

variable {V : Type u₁} {D : Type u₂} [Category.{v₁} V] [Category.{v₂} D]
  [MonoidalCategory V] (H : V ⥤ D ⥤ D)

/-- 作用の値域を固定したパラメータ関手。 -/
abbrev parameterFunctor (E : D) : V ⥤ D where
  obj X := (H.obj X).obj E
  map f := (H.map f).app E
  map_id X := by rw [H.map_id]; rfl
  map_comp f g := by rw [H.map_comp]; rfl

variable (u : H.obj (𝟙_ V) ≅ 𝟭 D)

/-- 写像対象の左単位の評価を、作用の単位と結同比較から計算する。 -/
lemma left_unit_evaluation {P Q : V} {E F : D} (h : 𝟙_ V ⟶ P)
    (v : (H.obj Q).obj E ⟶ F) (w : (H.obj P).obj F ⟶ F)
    (b : (parameterFunctor H E).obj (P ⊗ Q) ⟶ (H.obj P).obj ((H.obj Q).obj E))
    (b₀ : (parameterFunctor H E).obj ((𝟙_ V) ⊗ Q) ⟶ (H.obj (𝟙_ V)).obj ((H.obj Q).obj E))
    (hb : (parameterFunctor H E).map (h ⊗ₘ 𝟙 Q) ≫ b = b₀ ≫ (H.map h).app ((H.obj Q).obj E))
    (hw : (H.map h).app F ≫ w = u.hom.app F)
    (hu : b₀ ≫ u.hom.app ((H.obj Q).obj E) = (parameterFunctor H E).map (λ_ Q).hom) :
    (parameterFunctor H E).map (h ⊗ₘ 𝟙 Q) ≫ b ≫ (H.obj P).map v ≫ w =
      (parameterFunctor H E).map (λ_ Q).hom ≫ v := by
  erw [← Category.assoc, ← Category.assoc, hb]
  simp only [Category.assoc]
  erw [← reassoc_of% ((H.map h).naturality v)]
  erw [hw, u.hom.naturality v, ← Category.assoc, hu]
  rfl

/-- 写像対象の右単位の評価を、作用の単位と結同比較から計算する。 -/
lemma right_unit_evaluation {P Q : V} {E F : D} (h : 𝟙_ V ⟶ Q)
    (v : (H.obj P).obj E ⟶ F) (w : (H.obj Q).obj E ⟶ E)
    (b : (parameterFunctor H E).obj (P ⊗ Q) ⟶ (H.obj P).obj ((H.obj Q).obj E))
    (b₀ : (parameterFunctor H E).obj (P ⊗ (𝟙_ V)) ⟶
      (H.obj P).obj ((H.obj (𝟙_ V)).obj E))
    (hb : (parameterFunctor H E).map (𝟙 P ⊗ₘ h) ≫ b =
      b₀ ≫ (H.obj P).map ((H.map h).app E))
    (hw : (H.map h).app E ≫ w = u.hom.app E)
    (hu : b₀ ≫ (H.obj P).map (u.hom.app E) = (parameterFunctor H E).map (ρ_ P).hom) :
    (parameterFunctor H E).map (𝟙 P ⊗ₘ h) ≫ b ≫ (H.obj P).map w ≫ v =
      (parameterFunctor H E).map (ρ_ P).hom ≫ v := by
  erw [← Category.assoc, ← Category.assoc, hb]
  simp only [Category.assoc]
  erw [← CategoryTheory.Functor.map_comp_assoc, hw, ← Category.assoc, hu]

end SerrePositivity.MappingUnitLaws

end MappingUnitLaws


/-! # 作用の五角形から得る写像対象の合成の結合性 -/

@[expose] public section MappingAssociativity
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

end MappingAssociativity


/-! # 通常の射から写像対象の点への対応と合成 -/

@[expose] public section MappingArrowComposition
universe v₁ v₂ u₁ u₂

namespace SerrePositivity.MappingArrowComposition

open CategoryTheory CategoryTheory.MonoidalCategory

variable {V : Type u₁} {D : Type u₂} [Category.{v₁} V] [Category.{v₂} D]
  [MonoidalCategory V] (H : V ⥤ D ⥤ D)
  (a : ∀ P Q : V, H.obj (P ⊗ Q) ≅ H.obj Q ⋙ H.obj P)
  (u : H.obj (𝟙_ V) ≅ 𝟭 D)

/-- 二つの通常の射の点を合成した後の評価の法則。 -/
def arrowCompositionEvaluationLaw {P Q : V} {E F G : D}
    (f : E ⟶ F) (g : F ⟶ G) (p : 𝟙_ V ⟶ P) (q : 𝟙_ V ⟶ Q)
    (v : (H.obj Q).obj E ⟶ F) (w : (H.obj P).obj F ⟶ G) : Prop :=
  (H.map (p ⊗ₘ q)).app E ≫ MappingAssociativity.compositionEvaluation H a P Q v w =
    (H.map (λ_ (𝟙_ V)).hom).app E ≫ u.hom.app E ≫ f ≫ g

/-- 結同比較の自然性と作用の単位により、点の合成の評価は元の射の合成になる。 -/
lemma arrow_composition_evaluation {P Q : V} {E F G : D}
    (f : E ⟶ F) (g : F ⟶ G) (p : 𝟙_ V ⟶ P) (q : 𝟙_ V ⟶ Q)
    (v : (H.obj Q).obj E ⟶ F) (w : (H.obj P).obj F ⟶ G)
    (hv : (H.map q).app E ≫ v = u.hom.app E ≫ f)
    (hw : (H.map p).app F ≫ w = u.hom.app F ≫ g)
    (ha : (H.map (p ⊗ₘ q)).app E ≫ (a P Q).hom.app E =
      (a (𝟙_ V) (𝟙_ V)).hom.app E ≫ (H.map p).app ((H.obj (𝟙_ V)).obj E) ≫
        (H.obj P).map ((H.map q).app E))
    (hu : (a (𝟙_ V) (𝟙_ V)).hom.app E ≫ (H.obj (𝟙_ V)).map (u.hom.app E) =
      (H.map (ρ_ (𝟙_ V)).hom).app E) :
    arrowCompositionEvaluationLaw H a u f g p q v w := by
  unfold arrowCompositionEvaluationLaw MappingAssociativity.compositionEvaluation
  rw [reassoc_of% ha, ← CategoryTheory.Functor.map_comp_assoc, hv]
  rw [← reassoc_of% ((H.map p).naturality (u.hom.app E ≫ f))]
  rw [hw]
  rw [(H.obj (𝟙_ V)).map_comp]
  simp only [Category.assoc]
  rw [reassoc_of% (u.hom.naturality f)]
  change (a (𝟙_ V) (𝟙_ V)).hom.app E ≫ (H.obj (𝟙_ V)).map (u.hom.app E) ≫
    u.hom.app E ≫ f ≫ g = _
  rw [reassoc_of% hu, ← unitors_equal]

/-- 表現性を使った通常の射と写像対象の点の合成の一致の等式。 -/
def representedArrowCompositionLaw {E F G : D} {U : D ⥤ V}
    (adj : MappingUnitLaws.parameterFunctor H E ⊣ U)
    {P Q : V} (f : E ⟶ F) (g : F ⟶ G) (p : 𝟙_ V ⟶ P) (q : 𝟙_ V ⟶ Q)
    (v : (H.obj Q).obj E ⟶ F) (w : (H.obj P).obj F ⟶ G) : Prop :=
  (λ_ (𝟙_ V)).inv ≫ (p ⊗ₘ q) ≫
    adj.homEquiv _ G (MappingAssociativity.compositionEvaluation H a P Q v w) =
      AdjunctionHomLaws.comparisonHomEquiv adj (u.app E) G (f ≫ g)

/-- 点の合成の評価を表現性で戻すと、元の射の合成に対応する。 -/
lemma represented_arrow_composition {E F G : D} {U : D ⥤ V}
    (adj : MappingUnitLaws.parameterFunctor H E ⊣ U)
    {P Q : V} (f : E ⟶ F) (g : F ⟶ G) (p : 𝟙_ V ⟶ P) (q : 𝟙_ V ⟶ Q)
    (v : (H.obj Q).obj E ⟶ F) (w : (H.obj P).obj F ⟶ G)
    (h : arrowCompositionEvaluationLaw H a u f g p q v w) :
    representedArrowCompositionLaw H a u adj f g p q v w := by
  unfold representedArrowCompositionLaw
  rw [AdjunctionHomLaws.comparisonHomEquiv_apply]
  apply (cancel_epi (λ_ (𝟙_ V)).hom).mp
  simp only [Iso.hom_inv_id_assoc]
  apply AdjunctionHomLaws.curry_pre_comparison_of_evaluation adj
  exact h

end SerrePositivity.MappingArrowComposition

end MappingArrowComposition
