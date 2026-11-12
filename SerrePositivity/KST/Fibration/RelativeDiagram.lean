module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.WeakEquivalences
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CoreKan

/-! # 図式成分ごとの Verdier 弱同値

各評価を商へ写して core の逆像を取る。全ての成分でこの条件を満たす
単体を保持し、実辺が成分ごとに W に属することと同定する。
S• の具体的な評価・再添字との接続は K-S• の公開界面を待つ。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration

/-- 指定した全評価の商像が core に属する単体の部分複体。 -/
def relativeDiagram {B C X : SSet.{u}} {J : Type v}
    (q : B ⟶ C) (ev : J → (X ⟶ B)) : X.Subcomplex where
  obj n := {s | ∀ j, (ev j ≫ q).app n s ∈ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore C).obj n}
  map {n m} f s hs := by
    intro j
    rw [NatTrans.naturality_apply]
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore C).map f (hs j)

/-- 相対図式は周囲の全ての頂点を含む。 -/
lemma relativeDiagram_vertex {B C X : SSet.{u}} {J : Type v}
    (q : B ⟶ C) (ev : J → (X ⟶ B)) (x : X _⦋0⦌) :
    x ∈ (relativeDiagram q ev).obj (Opposite.op ⦋0⦌) :=
  fun _j => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore_vertex _

/-- 相対図式の辺は、指定評価の全てで W に属する実辺と一致する。 -/
lemma relativeDiagram_mem_edge_iff
    {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C}
    (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q) {X : SSet.{u}} {J : Type v}
    (ev : J → (X ⟶ B.obj)) (s : X _⦋1⦌) :
    s ∈ (relativeDiagram q.hom ev).obj (Opposite.op ⦋1⦌) ↔
      ∀ j, (ev j).app (Opposite.op ⦋1⦌) s ∈ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i := by
  change (∀ j, (ev j ≫ q.hom).app _ s ∈ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore C.obj).obj _) ↔ _
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore_mem_edge_iff]
  apply forall_congr'
  intro j
  have he := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.mem_weakEquivalences_iff_invertible h
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex ((ev j).app (Opposite.op ⦋1⦌) s))
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr
    (e := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex ((ev j).app _ s)).map ((truncation 2).map q.hom))
    (f := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex ((ev j ≫ q.hom).app _ s)) rfl).symm.trans he.symm

/-- 一般単体も全ての一次制限の成分ごとの W 所属で判定する。 -/
lemma relativeDiagram_mem_iff
    {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C}
    (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q) {X : SSet.{u}} {J : Type v}
    (ev : J → (X ⟶ B.obj)) {n : SimplexCategoryᵒᵖ} (s : X.obj n) :
    s ∈ (relativeDiagram q.hom ev).obj n ↔
      ∀ j, ∀ f : ⦋1⦌ ⟶ n.unop,
        (ev j).app (Opposite.op ⦋1⦌) (X.map f.op s) ∈ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i := by
  change (∀ j, ∀ f : ⦋1⦌ ⟶ n.unop,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (C.obj.map f.op ((ev j ≫ q.hom).app n s)))) ↔ _
  apply forall_congr'
  intro j
  apply forall_congr'
  intro f
  rw [← NatTrans.naturality_apply]
  have he := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.mem_weakEquivalences_iff_invertible h
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex ((ev j).app _ (X.map f.op s)))
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr
    (e := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex ((ev j).app _ (X.map f.op s))).map ((truncation 2).map q.hom))
    (f := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex ((ev j ≫ q.hom).app _ (X.map f.op s))) rfl).symm.trans he.symm

/-- 各評価の商像を core に取る実際の射。 -/
def relativeDiagramEvaluation {B C X : SSet.{u}} {J : Type v}
    (q : B ⟶ C) (ev : J → (X ⟶ B)) (j : J) :
    (relativeDiagram q ev : SSet.{u}) ⟶ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore C : SSet.{u}) :=
  Subcomplex.lift ((relativeDiagram q ev).ι ≫ ev j ≫ q) (by
    rintro n _ ⟨s, rfl⟩
    exact s.property j)

/-- 評価を含めると元の図式の商像を厳密に回収する。 -/
lemma relativeDiagramEvaluation_ι {B C X : SSet.{u}} {J : Type v}
    (q : B ⟶ C) (ev : J → (X ⟶ B)) (j : J) :
    relativeDiagramEvaluation q ev j ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore C).ι =
      (relativeDiagram q ev).ι ≫ ev j ≫ q := rfl

/-- 周囲の内ホーン充填は全成分の core 条件を保持する。 -/
instance relativeDiagram_quasicategory {B C X : SSet.{u}} [Quasicategory X]
    {J : Type v} (q : B ⟶ C) (ev : J → (X ⟶ B)) :
    Quasicategory (relativeDiagram q ev : SSet.{u}) where
  hornFilling' {n i} a h₀ hlast := by
    obtain ⟨F, hF⟩ := Quasicategory.hornFilling h₀ hlast
      (a ≫ (relativeDiagram q ev).ι)
    have hm : SSet.yonedaEquiv F ∈ (relativeDiagram q ev).obj _ := by
      intro j
      have he : (horn (n + 2) i).ι ≫ (F ≫ ev j ≫ q) =
          (a ≫ relativeDiagramEvaluation q ev j) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore C).ι := by
        rw [← Category.assoc, ← Category.assoc, ← hF]
        rfl
      exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.quasicategoryCore_horn_filler_mem n i
        (a ≫ relativeDiagramEvaluation q ev j) (F ≫ ev j ≫ q) he
    let G : Δ[n + 2] ⟶ (relativeDiagram q ev : SSet.{u}) :=
      SSet.yonedaEquiv.symm ⟨SSet.yonedaEquiv F, hm⟩
    have hG : G ≫ (relativeDiagram q ev).ι = F := by
      apply SSet.yonedaEquiv.injective
      rw [SSet.yonedaEquiv_comp]
      change (SSet.yonedaEquiv G).val = SSet.yonedaEquiv F
      rw [Equiv.apply_symm_apply]
    refine ⟨G, ?_⟩
    apply (cancel_mono (relativeDiagram q ev).ι).1
    rw [Category.assoc, hG]
    exact hF

end SerrePositivity.KST.Fibration
