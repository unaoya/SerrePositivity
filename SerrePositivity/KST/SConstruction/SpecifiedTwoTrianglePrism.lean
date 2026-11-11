module
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalencePathInnerFibration
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.F1DiagramsTrianglePrism

/-!
概要：元の二三角形と指定二短辺の比較を同時に保つ prism を構成する。
方針：二短辺を同じ内ホーンへ貼り、両端固定の内ホーン延長を使う。
規約：元の二単体を選び直さず、共有中間頂点の経路を厳密に保持する。
使われ方：恒等実右面の上下二単体を指定四辺比較へ接続する。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet InfinityCategories
open scoped Simplicial
variable {X : SSet.{u}} [Quasicategory X]
variable (f g : (Δ[2] : SSet.{u}) ⟶ X)
  (H₂ : SSet.Homotopy (stdSimplex.δ (2 : Fin 3) ≫ f) (stdSimplex.δ (2 : Fin 3) ≫ g))
  (H₀ : SSet.Homotopy (stdSimplex.δ (0 : Fin 3) ≫ f) (stdSimplex.δ (0 : Fin 3) ≫ g))
  (hw : (stdSimplex.δ (0 : Fin 2) ▷ (Δ[1] : SSet.{u})) ≫ H₂.h =
    (stdSimplex.δ (1 : Fin 2) ▷ (Δ[1] : SSet.{u})) ≫ H₀.h)

/-- 概要：元二短辺の全比較を同じ共有頂点で内ホーンへ貼る。
方針：内二ホーンの積を取った pushout を使う。
規約：元の二側面を保持。使われ方：指定二三角形の比較 prism の側面入力。 -/
def specifiedTwoTriangleHorn : (horn 2 1 : SSet.{u}) ⊗ Δ[1] ⟶ X :=
  (horn₂₁.isPushout.map (tensorRight (Δ[1] : SSet.{u}))).desc H₂.h H₀.h hw

/-- 概要：同じ内ホーン比較の二短辺は指定した全比較。
方針：元 pushout の両包含を回収する。
規約：全単体の等号。使われ方：二短辺の保持。 -/
lemma specifiedTwoTriangleHorn_faces :
    (horn₂₁.ι₀₁ ▷ (Δ[1] : SSet.{u})) ≫ specifiedTwoTriangleHorn f g H₂ H₀ hw = H₂.h ∧
    (horn₂₁.ι₁₂ ▷ (Δ[1] : SSet.{u})) ≫ specifiedTwoTriangleHorn f g H₂ H₀ hw = H₀.h :=
  ⟨(horn₂₁.isPushout.map (tensorRight (Δ[1] : SSet.{u}))).inl_desc _ _ _,
    (horn₂₁.isPushout.map (tensorRight (Δ[1] : SSet.{u}))).inr_desc _ _ _⟩

/-- 概要：元内ホーンの全比較は指定した両二単体の制限を端点に持つ。
方針：元 pushout の二短辺で全写像の等号を検出する。
規約：両端の元三角形を固定。使われ方：両端固定 prism 延長の入力。 -/
lemma specifiedTwoTriangleHorn_endpoints :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (horn 2 1 : SSet.{u}) ≫
        (β_ Δ[1] (horn 2 1 : SSet.{u})).hom ≫ specifiedTwoTriangleHorn f g H₂ H₀ hw =
      (horn 2 1).ι ≫ f ∧
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (horn 2 1 : SSet.{u}) ≫
        (β_ Δ[1] (horn 2 1 : SSet.{u})).hom ≫ specifiedTwoTriangleHorn f g H₂ H₀ hw =
      (horn 2 1).ι ≫ g := by
  constructor
  all_goals apply horn₂₁.isPushout.hom_ext
  · rw [← Category.assoc (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 _) _, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.prismEndpoint_zero_braiding,
      ← Category.assoc, ← SSet.ι₀_comp, Category.assoc,
      (specifiedTwoTriangleHorn_faces f g H₂ H₀ hw).1, H₂.h₀,
      ← Category.assoc, horn.ι_ι]
  · rw [← Category.assoc (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 _) _, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.prismEndpoint_zero_braiding,
      ← Category.assoc, ← SSet.ι₀_comp, Category.assoc,
      (specifiedTwoTriangleHorn_faces f g H₂ H₀ hw).2, H₀.h₀,
      ← Category.assoc, horn.ι_ι]
  · rw [← Category.assoc (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 _) _, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.prismEndpoint_one_braiding,
      ← Category.assoc, ← SSet.ι₁_comp, Category.assoc,
      (specifiedTwoTriangleHorn_faces f g H₂ H₀ hw).1, H₂.h₁,
      ← Category.assoc, horn.ι_ι]
  · rw [← Category.assoc (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 _) _, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.prismEndpoint_one_braiding,
      ← Category.assoc, ← SSet.ι₁_comp, Category.assoc,
      (specifiedTwoTriangleHorn_faces f g H₂ H₀ hw).2, H₀.h₁,
      ← Category.assoc, horn.ι_ι]

/-- 概要：元二単体と指定二短辺の全比較を同時に保持する実 prism が存在する。
方針：同じ内ホーン比較を両端固定の既存延長へ渡す。
規約：元二単体・元二側面の全単体を保持。使われ方：恒等実右面の上下面比較。 -/
lemma exists_specifiedTwoTrianglePrism :
    ∃ P : (Δ[1] ⊗ Δ[2] : SSet.{u}) ⟶ X,
      (Δ[1] ◁ (horn 2 1).ι) ≫ P =
        (β_ Δ[1] (horn 2 1 : SSet.{u})).hom ≫ specifiedTwoTriangleHorn f g H₂ H₀ hw ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 Δ[2] ≫ P = f ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 Δ[2] ≫ P = g :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.prism_extend_innerHorn_with_endpoints (1 : Fin 3) (by decide) (by decide) _ f g
    (specifiedTwoTriangleHorn_endpoints f g H₂ H₀ hw).1
    (specifiedTwoTriangleHorn_endpoints f g H₂ H₀ hw).2
/-- 概要：同じ元両二単体と指定二側面を保つ比較 prism。
方針：元存在証明から制限式ごと選ぶ。
規約：元全単体を保持。使われ方：上下面の全比較。 -/
def specifiedTwoTrianglePrism : (Δ[1] ⊗ Δ[2] : SSet.{u}) ⟶ X :=
  (exists_specifiedTwoTrianglePrism f g H₂ H₀ hw).choose

/-- 概要：同じ比較 prism は元ホーン側面と元二単体を回収する。
方針：元存在証明の指定制限式を使う。
規約：全単体の厳密等号。使われ方：全比較の元境界照合。 -/
lemma specifiedTwoTrianglePrism_restrictions :
    (Δ[1] ◁ (horn 2 1).ι) ≫ specifiedTwoTrianglePrism f g H₂ H₀ hw =
        (β_ Δ[1] (horn 2 1 : SSet.{u})).hom ≫ specifiedTwoTriangleHorn f g H₂ H₀ hw ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 Δ[2] ≫ specifiedTwoTrianglePrism f g H₂ H₀ hw = f ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 Δ[2] ≫ specifiedTwoTrianglePrism f g H₂ H₀ hw = g :=
  (exists_specifiedTwoTrianglePrism f g H₂ H₀ hw).choose_spec

/-- 概要：元二単体を結ぶ同じ全ホモトピー。
方針：元 prism の二因子を交換する。
規約：元二単体を選び直さない。使われ方：全二胞体の比較。 -/
def specifiedTwoTriangleHomotopy : SSet.Homotopy f g where
  h := (β_ (Δ[2] : SSet.{u}) Δ[1]).hom ≫ specifiedTwoTrianglePrism f g H₂ H₀ hw
  h₀ := (specifiedTwoTrianglePrism_restrictions f g H₂ H₀ hw).2.1
  h₁ := (specifiedTwoTrianglePrism_restrictions f g H₂ H₀ hw).2.2
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.property

/-- 概要：同じ全二胞体比較は指定した内ホーン全比較を厳密に回収する。
方針：元 prism の制限と因子交換の自然性を使う。
規約：二短辺を同時保持。使われ方：上下二胞体の境界の貼り合わせ。 -/
lemma specifiedTwoTriangleHomotopy_horn :
    ((horn 2 1).ι ▷ (Δ[1] : SSet.{u})) ≫
        (specifiedTwoTriangleHomotopy f g H₂ H₀ hw).h =
      specifiedTwoTriangleHorn f g H₂ H₀ hw := by
  have hs : ((horn 2 1).ι ▷ (Δ[1] : SSet.{u})) ≫ (β_ Δ[2] Δ[1]).hom =
      (β_ (horn 2 1 : SSet.{u}) Δ[1]).hom ≫ (Δ[1] ◁ (horn 2 1).ι) := rfl
  change ((horn 2 1).ι ▷ (Δ[1] : SSet.{u})) ≫ (β_ Δ[2] Δ[1]).hom ≫ _ = _
  rw [← Category.assoc, hs, Category.assoc,
    (specifiedTwoTrianglePrism_restrictions f g H₂ H₀ hw).1]
  rfl

/-- 概要：同じ全二胞体比較の二短辺側面は元の指定全ホモトピー。
方針：同じ内ホーン制限を元の二包含で回収する。
規約：全単体で一致。使われ方：全四角形比較における指定境界の保持。 -/
lemma specifiedTwoTriangleHomotopy_faces :
    (stdSimplex.δ (2 : Fin 3) ▷ (Δ[1] : SSet.{u})) ≫
        (specifiedTwoTriangleHomotopy f g H₂ H₀ hw).h = H₂.h ∧
    (stdSimplex.δ (0 : Fin 3) ▷ (Δ[1] : SSet.{u})) ≫
        (specifiedTwoTriangleHomotopy f g H₂ H₀ hw).h = H₀.h := by
  constructor
  · have he := congrArg
      (fun k : (Δ[1] : SSet.{u}) ⟶ Δ[2] =>
        (k ▷ (Δ[1] : SSet.{u})) ≫ (specifiedTwoTriangleHomotopy f g H₂ H₀ hw).h)
      (horn.ι_ι (1 : Fin 3) (2 : Fin 3) (by decide))
    apply he.symm.trans
    rw [comp_whiskerRight, Category.assoc, specifiedTwoTriangleHomotopy_horn]
    exact (specifiedTwoTriangleHorn_faces f g H₂ H₀ hw).1
  · have he := congrArg
      (fun k : (Δ[1] : SSet.{u}) ⟶ Δ[2] =>
        (k ▷ (Δ[1] : SSet.{u})) ≫ (specifiedTwoTriangleHomotopy f g H₂ H₀ hw).h)
      (horn.ι_ι (1 : Fin 3) (0 : Fin 3) (by decide))
    apply he.symm.trans
    rw [comp_whiskerRight, Category.assoc, specifiedTwoTriangleHomotopy_horn]
    exact (specifiedTwoTriangleHorn_faces f g H₂ H₀ hw).2

end SerrePositivity.KST.SConstruction
