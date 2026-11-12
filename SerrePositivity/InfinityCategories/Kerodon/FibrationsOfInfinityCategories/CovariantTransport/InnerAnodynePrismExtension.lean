module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CartesianEdge

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.InnerAnodyneReplacement
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.InnerAnodyneVertices
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.PrismVerticalSimplex
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IntervalBoundary
public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Inner.PushoutProduct

/-!
概要：inner anodyne な置換に沿う、両端を固定した区間上の prism の延長。
方針：区間の境界との pushout-product の inner anodyne 性を使い、全単射な頂点で垂直辺の条件を戻す。
規約：射影 p は区間上の inner fibration。
使われ方：Kerodon Theorem 5.2.4.1（Tag 024N）、写像円柱の因子の quasicategory への置換。

対応節は Kerodon 5.2（Tag 019A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport

/-- 概要：二端点の境界図式の後合成は端点の後合成で計算できる。
方針：境界の時刻が零か一かで場合分けする。
規約：パラメータの単体集合は任意。
使われ方：Kerodon Theorem 5.2.4.1（Tag 024N）、prism の延長の基底との整合性。 -/
lemma intervalBoundaryDiagram_postcomp {A E F : SSet.{u}} (a b : A ⟶ E) (f : E ⟶ F) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram a b ≫ f = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram (a ≫ f) (b ≫ f) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨t, x⟩
  change f.app (Opposite.op ⦋n⦌) (if t.val 0 = 0 then a.app _ x else b.app _ x) =
    (if t.val 0 = 0 then f.app _ (a.app _ x) else f.app _ (b.app _ x))
  split <;> rfl

/-- 概要：inner anodyne な射に沿い、両端と区間への射影を保った prism を延長できる。
方針：既存の prism と新しい二端点の図式を押し出しで貼り、内ホーンの持ち上げを使う。
規約：F0 と F1 の基底の値はそれぞれ零・一。
使われ方：Kerodon Theorem 5.2.4.1（Tag 024N）、因子の置換に伴う比較図式の延長。 -/
lemma innerAnodyne_extend_prism_over_interval {A B E : SSet.{u}}
    (i : A ⟶ B) (hi : innerAnodyneExtensions i)
    (p : E ⟶ (Δ[1] : SSet.{u})) [InnerFibration p]
    (H : (Δ[1] : SSet.{u}) ⊗ A ⟶ E) (hH : H ≫ p = fst Δ[1] A)
    (F0 F1 : B ⟶ E)
    (h0 : i ≫ F0 = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 A ≫ H) (h1 : i ≫ F1 = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 A ≫ H)
    (h0p : F0 ≫ p = SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))
    (h1p : F1 ≫ p = SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) :
    ∃ L : (Δ[1] : SSet.{u}) ⊗ B ⟶ E,
      (Δ[1] ◁ i) ≫ L = H ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 B ≫ L = F0 ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 B ≫ L = F1 ∧ L ≫ p = fst Δ[1] B := by
  let sq := Functor.PushoutObjObj.ofHasPushout (curriedTensor SSet.{u}) (boundary 1).ι i
  have hw : ((boundary 1).ι ▷ A) ≫ H =
      ((boundary 1 : SSet.{u}) ◁ i) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram F0 F1 := by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram_naturality, h0, h1, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram_restrict]
  let C := sq.isPushout.desc H (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram F0 F1) hw
  have hsql : sq.inl ≫ sq.ι = Δ[1] ◁ i := sq.inl_ι
  have hsqr : sq.inr ≫ sq.ι = (boundary 1).ι ▷ B := sq.inr_ι
  have hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram F0 F1 ≫ p = ((boundary 1).ι ▷ B) ≫ fst Δ[1] B := by
    rw [intervalBoundaryDiagram_postcomp, h0p, h1p, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram_restrict]
    simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint, lift_fst]
  have hC : C ≫ p = sq.ι ≫ fst Δ[1] B := by
    apply sq.hom_ext
    · simp only [C, ← Category.assoc, sq.isPushout.inl_desc, hsql, whiskerLeft_fst]
      exact hH
    · simp only [C, ← Category.assoc, sq.isPushout.inr_desc, hsqr]
      exact hb
  have := (innerAnodyneExtensions_pushoutObjObjι sq hi) p (InnerFibration.mem (q := p))
  let t : CommSq C sq.ι p (fst Δ[1] B) := ⟨hC⟩
  have hL : (Δ[1] ◁ i) ≫ t.lift = H := by
    rw [← hsql, Category.assoc, t.fac_left]
    exact sq.isPushout.inl_desc _ _ _
  have hB : ((boundary 1).ι ▷ B) ≫ t.lift = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram F0 F1 := by
    rw [← hsqr, Category.assoc, t.fac_left]
    exact sq.isPushout.inr_desc _ _ _
  refine ⟨t.lift, hL, ?_, ?_, t.fac_right⟩
  · rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryEndpoint_ι (0 : Fin 2) B, Category.assoc, hB,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram_zero]
  · rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryEndpoint_ι (1 : Fin 2) B, Category.assoc, hB,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram_one]

/-- 概要：prism の垂直辺の評価は係数の射に自然。
方針：頂点の定値一単体に対する射の自然性を使う。
規約：単体集合の充填性は要求しない。
使われ方：Kerodon Theorem 5.2.4.1（Tag 024N）、延長した prism の垂直辺の条件。 -/
lemma prismVerticalSimplex_naturality {A B E : SSet.{u}} (i : A ⟶ B)
    (H : (Δ[1] : SSet.{u}) ⊗ B ⟶ E) (x : A _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.prismVerticalSimplex ((Δ[1] ◁ i) ≫ H) x =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.prismVerticalSimplex H (i.app (Opposite.op ⦋0⦌) x) := by
  change H.app (Opposite.op ⦋1⦌)
    (stdSimplex.objEquiv.symm (𝟙 ⦋1⦌), i.app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x 1)) = _
  rw [show i.app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x 1) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (i.app (Opposite.op ⦋0⦌) x) 1 from
      ConcreteCategory.congr_hom (C := Type u)
        (i.naturality (SimplexCategory.const ⦋1⦌ ⦋0⦌ 0).op) x]
  rfl

/-- 概要：inner anodyne な置換後の prism の垂直辺の cocartesian 性は元の条件から従う。
方針：置換先の各頂点を元の頂点から持ち上げ、垂直辺の自然性を使う。
規約：延長 L の制限は元の H と厳密に一致する。
使われ方：Kerodon Theorem 5.2.4.1（Tag 024N）、一般の因子から quasicategory の因子への還元。 -/
lemma innerAnodyne_prism_vertical_isCocartesian {A B E S : SSet.{u}}
    (i : A ⟶ B) (hi : innerAnodyneExtensions i) (p : E ⟶ S)
    (H : (Δ[1] : SSet.{u}) ⊗ A ⟶ E) (L : (Δ[1] : SSet.{u}) ⊗ B ⟶ E)
    (hL : (Δ[1] ◁ i) ≫ L = H)
    (hc : ∀ x : A _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge p (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.prismVerticalSimplex H x)) :
    ∀ y : B _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge p (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.prismVerticalSimplex L y) := by
  intro y
  obtain ⟨x, rfl⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.innerAnodyne_vertex_bijective i hi).surjective y
  rw [← prismVerticalSimplex_naturality, hL]
  exact hc x

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport
