module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.FullSubcomplexFibration
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FullyFaithful

/-!
概要：頂点条件の全部分複体の包含の写像空間による充満忠実性。
方針：pinched 単体の全頂点が両端のいずれかであることから、元の単体を持ち上げる。
規約：quasicategory 性や頂点条件の同型不変性は不要。
使われ方：B2 の反射的部分圏の包含に対する充満忠実性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories

/-- 概要：両端が全部分複体に属する pinched 単体はその全部分複体に属する。
方針：任意の頂点を先頭面の頂点または最終頂点に分ける。
規約：全次数で成立する。使われ方：写像空間の包含の逆射。 -/
lemma fullSubcomplex_pinchedSimplex_mem {X : SSet.{u}} (P : X _⦋0⦌ → Prop)
    (x y : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X P : SSet.{u}) _⦋0⦌) {n : ℕ}
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.Simplex x.val y.val n) :
    s.val ∈ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X P).obj (Opposite.op ⦋n + 1⦌) := by
  intro v
  by_cases hv : v = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.lastVertex n
  · rw [hv, s.target]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex y
  · have hk : (v.toOrderHom 0).val < n + 1 := by
      by_contra hn
      apply hv
      apply SimplexCategory.Hom.ext
      ext i
      have hi : i = 0 := by
        apply Fin.ext
        change i.val = 0
        have h := i.isLt
        change i.val < 1 at h
        omega
      subst i
      change (v.toOrderHom 0).val = n + 1
      have hh := (v.toOrderHom 0).isLt
      change (v.toOrderHom 0).val < n + 2 at hh
      omega
    let w : ⦋0⦌ ⟶ ⦋n⦌ := SimplexCategory.const _ _ ⟨(v.toOrderHom 0).val, hk⟩
    have hf : w ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.front n = v := by
      apply SimplexCategory.Hom.ext
      ext i
      have hi : i = 0 := by
        apply Fin.ext
        change i.val = 0
        have h := i.isLt
        change i.val < 1 at h
        omega
      subst i
      rfl
    rw [← hf, op_comp, CategoryTheory.Functor.map_comp_apply, s.source,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant_pullback, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex x

/-- 概要：全部分複体内の両端を持つ pinched 単体を一意に持ち上げる。
方針：元の単体に全頂点の条件を付け、両端の式は部分型の外延性で回収する。
規約：元の単体そのものを保つ。使われ方：写像空間の包含の逆の各次数。 -/
def fullSubcomplexPinchedSimplexLift {X : SSet.{u}} (P : X _⦋0⦌ → Prop)
    (x y : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X P : SSet.{u}) _⦋0⦌) {n : ℕ}
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.Simplex x.val y.val n) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.Simplex x y n where
  val := ⟨s.val, fullSubcomplex_pinchedSimplex_mem P x y s⟩
  source := by apply Subtype.ext; exact s.source
  target := by apply Subtype.ext; exact s.target

/-- 概要：全部分複体の包含の pinched 写像空間の射の逆。
方針：全次数で pinched 単体を持ち上げ、面・退化は元の単体の式で確認する。
規約：quasicategory 性は不要。使われ方：包含の充満忠実性。 -/
def fullSubcomplexPinchedInverse {X : SSet.{u}} (P : X _⦋0⦌ → Prop)
    (x y : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X P : SSet.{u}) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom x.val y.val ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom x y where
  app _ := ↾fullSubcomplexPinchedSimplexLift P x y
  naturality {_ _} _ := by
    apply ConcreteCategory.hom_ext
    intro s
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.Simplex.ext
    apply Subtype.ext
    rfl

/-- 概要：全部分複体の包含は各 pinched 写像空間の厳密な同型を与える。
方針：持ち上げによる逆と元の単体への忘却の両合成を比較する。
規約：P の同型不変性も quasicategory 性も不要。
使われ方：反射的部分圏の包含の充満忠実性を公理なしで供給する。 -/
def fullSubcomplexPinchedIso {X : SSet.{u}} (P : X _⦋0⦌ → Prop)
    (x y : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X P : SSet.{u}) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom x y ≅ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom x.val y.val where
  hom := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X P).ι x y
  inv := fullSubcomplexPinchedInverse P x y
  hom_inv_id := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro s
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.Simplex.ext
    apply Subtype.ext
    rfl
  inv_hom_id := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro s
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.Simplex.ext
    rfl

/-- 概要：頂点条件で定義した全部分複体の包含は充満忠実。
方針：各 pinched 写像空間の厳密な同型を実際のホモトピー同値へ移す。
規約：これは h の充満忠実性だけを述べる定理ではない。
使われ方：B2 の左随伴を持つ包含の余単位を可逆にする一般補題の入力。 -/
lemma isFullyFaithful_fullSubcomplexOnVertices_ι (X : SSet.{u}) (P : X _⦋0⦌ → Prop) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X P).ι := by
  intro x y
  let e := fullSubcomplexPinchedIso P x y
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence e.hom
  refine ⟨e.inv, ?_, ?_⟩
  · rw [e.hom_inv_id]
    exact ⟨SSet.RelativeMorphism.Homotopy.refl (SSet.RelativeMorphism.botEquiv.symm (𝟙 _))⟩
  · rw [e.inv_hom_id]
    exact ⟨SSet.RelativeMorphism.Homotopy.refl (SSet.RelativeMorphism.botEquiv.symm (𝟙 _))⟩

end SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories
