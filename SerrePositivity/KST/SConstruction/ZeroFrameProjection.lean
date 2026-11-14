module
public import SerrePositivity.KST.SConstruction.ZeroFrame

/-! # 零対角の枠から第一行への射影
概要：零対角を持つ枠の図式を第一行に制限する。
方針：零次元は頂点を指定して延長し、正次元は相対境界延長を使う。
規約：cofiber 条件を加える前の中間段階。使われ方：第一行の trivial Kan fibration。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：対角上で零対象となる枠の関手頂点。
方針：各対角頂点で内部 Hom を評価する。
規約：枠の他の頂点には条件を課さない。使われ方：零対角の coherent な選択。 -/
def IsZeroFrameVertex {n : ℕ} {C : SSet.{u}}
    (v : ((ihom (frameNerve n)).obj C) _⦋0⦌) : Prop :=
  ∀ x : (frameNerve n) _⦋0⦌, IsDiagonal (nerveEquiv x).val →
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt x).app (Opposite.op ⦋0⦌) v)

/-- 概要：零対角を持つ全ての枠の図式。
方針：内部 Hom の全部分複体。
規約：零対象は固定せず動かす。使われ方：第一行制限の中間図式圏。 -/
def zeroFrameDiagrams (n : ℕ) (C : SSet.{u}) : SSet.{u} :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices ((ihom (frameNerve n)).obj C) IsZeroFrameVertex : SSet.{u})

/-- 概要：零対角を持つ枠から第一行への制限。
方針：全部分複体の包含の後で前合成する。
規約：第一行は枠内の充満部分複体。使われ方：零対角の選択を忘れる射影。 -/
def zeroFrameProjection (n : ℕ) (C : SSet.{u}) :
    zeroFrameDiagrams n C ⟶ (ihom (framePositiveRow n : SSet.{u})).obj C :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ IsZeroFrameVertex).ι ≫ (pre (framePositiveRow n).ι).app C

/-- 概要：対角は正の第一行に属さない。
方針：左端零と端点の等号は右端の正性に矛盾する。
規約：任意の Ar 頂点。使われ方：追加する対角の頂点の指定。 -/
lemma diagonal_not_positiveRow {n : ℕ} {a : Ar.{u} n} (hd : IsDiagonal a) : ¬ IsPositiveRow a := by
  intro h
  have he : a.down.val.2 = 0 := hd.symm.trans h.1
  exact (ne_of_gt h.2) he

/-- 概要：枠の対角頂点は第一行部分複体の外にある。
方針：全部分複体の頂点条件と端点の等号を使う。
規約：零次元の条件を明示する。使われ方：零対角の新しい頂点。 -/
lemma diagonal_not_mem_framePositiveRow {n : ℕ} (x : (frameNerve.{u} n) _⦋0⦌)
    (hd : IsDiagonal (nerveEquiv x).val) :
    x ∉ (framePositiveRow n).obj (Opposite.op ⦋0⦌) := by
  intro hx
  exact diagonal_not_positiveRow hd (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex ⟨x, hx⟩)

/-- 概要：任意の第一行は零対角を持つ枠に延長できる。
方針：既存頂点の像を保ち、対角に零対象を指定して混合端点延長を使う。
規約：値域の quasicategory 性は不要。使われ方：零次元の持ち上げ。 -/
lemma exists_zeroFrame_extension {C : SSet.{u}} [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.HasZeroVertex C] (n : ℕ)
    (f : (framePositiveRow n : SSet.{u}) ⟶ C) :
    ∃ F : frameNerve n ⟶ C, (framePositiveRow n).ι ≫ F = f ∧
      ∀ x : (frameNerve n) _⦋0⦌, IsDiagonal (nerveEquiv x).val →
        _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (F.app (Opposite.op ⦋0⦌) x) := by
  classical
  let z := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.chosenZeroVertex C
  let x : (frameNerve n) _⦋0⦌ → C _⦋0⦌ := fun v ↦
    if h : v ∈ (framePositiveRow n).obj (Opposite.op ⦋0⦌) then
      f.app (Opposite.op ⦋0⦌) ⟨v, h⟩ else z.vertex
  have hx (v : (framePositiveRow n : SSet.{u}) _⦋0⦌) :
      x v.val = f.app (Opposite.op ⦋0⦌) v := by
    dsimp [x]
    rw [dite_eq_left v.property]
    rfl
  have hxd (v : (frameNerve n) _⦋0⦌) (hd : IsDiagonal (nerveEquiv v).val) :
      x v = z.vertex := by
    dsimp [x]
    rw [dite_eq_right (diagonal_not_mem_framePositiveRow v hd)]
  obtain ⟨F, hF, hv⟩ := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.exists_extension_with_vertices (framePositiveRow n) f x hx (by
    intro m s hs
    rcases frameNerve_diagonal_endpoint s hs with hi | ht
    · rw [hxd _ hi]
      exact Or.inl z.isInitial
    · rw [hxd _ ht]
      exact Or.inr z.isTerminal)
  refine ⟨F, hF, ?_⟩
  intro v hd
  rw [hv, hxd v hd]
  exact z.isZero

/-- 概要：零対角の枠を忘れる射影は trivial Kan fibration。
方針：零次元は零頂点を指定した延長、正次元は枠の境界延長で充填する。
規約：HasZeroVertex だけを要求し、cofiber 条件はまだ課さない。
使われ方：第一行から gapped 図式を復元する第一段階。 -/
instance zeroFrameProjection_trivialKanFibration (n : ℕ) (C : SSet.{u}) [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.HasZeroVertex C] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (zeroFrameProjection n C) := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.trivialKanFibration_iff_boundary _).2
  intro d
  constructor
  intro a b sq
  let ι : zeroFrameDiagrams n C ⟶ (ihom (frameNerve n)).obj C :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ IsZeroFrameVertex).ι
  cases d with
  | zero =>
    let f := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (framePositiveRow n : SSet.{u}) C).symm (SSet.yonedaEquiv b)
    obtain ⟨F, hF, hz⟩ := exists_zeroFrame_extension n f
    let v : (zeroFrameDiagrams n C) _⦋0⦌ := ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F, by
      intro α
      have hα : α = 𝟙 ⦋0⦌ := Subsingleton.elim _ _
      rw [hα, op_id, CategoryTheory.Functor.map_id_apply]
      intro x hd
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_functorVertex]
      exact hz x hd⟩
    refine CommSq.HasLift.mk' {
      l := SSet.yonedaEquiv.symm v
      fac_left := boundary.hom_ext₀
      fac_right := ?_ }
    apply SSet.yonedaEquiv.injective
    rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
    change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((framePositiveRow n).ι ≫ F) = SSet.yonedaEquiv b
    rw [hF]
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ C).apply_symm_apply _
  | succ d =>
    let H := uncurry (a ≫ ι)
    let G := uncurry b
    have hC : curry H = a ≫ ι := curry_uncurry _
    have hw : ((framePositiveRow n).ι ▷ (boundary (d + 1) : SSet.{u})) ≫ H =
        ((framePositiveRow n : SSet.{u}) ◁ (boundary (d + 1)).ι) ≫ G := by
      have hh := congrArg uncurry sq.w
      change uncurry ((a ≫ ι) ≫ (pre (framePositiveRow n).ι).app C) =
        uncurry ((boundary (d + 1)).ι ≫ b) at hh
      rw [uncurry_pre_app, uncurry_natural_left] at hh
      exact hh
    have hz (x : (frameNerve n) _⦋0⦌) (hd : IsDiagonal (nerveEquiv x).val)
        (v : (boundary (d + 1) : SSet.{u}) _⦋0⦌) :
        _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (H.app (Opposite.op ⦋0⦌) (x, v)) := by
      have hh := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex (a.app (Opposite.op ⦋0⦌) v) x hd
      change _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex ((a.app (Opposite.op ⦋0⦌) v).val.app
        (Opposite.op ⦋0⦌) (𝟙 _) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x 0)) at hh
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero] at hh
      exact hh
    obtain ⟨F, hF, hFG⟩ := zeroFrame_extend_boundary n d H G hw hz
    have hc : (boundary (d + 1)).ι ≫ curry F = a ≫ ι := by
      rw [← curry_natural_left, hF, hC]
    have hv (v : (Δ[d + 1] : SSet.{u}) _⦋0⦌) :
        IsZeroFrameVertex ((curry F).app (Opposite.op ⦋0⦌) v) := by
      let w : (boundary (d + 1) : SSet.{u}) _⦋0⦌ := ⟨v, by
        have h := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.vertex_mem_boundary.{u} d (stdSimplex.obj₀Equiv.{u} v)
        rw [Equiv.symm_apply_apply] at h
        exact h⟩
      have hh := ConcreteCategory.congr_hom (NatTrans.congr_app hc (Opposite.op ⦋0⦌)) w
      change (curry F).app (Opposite.op ⦋0⦌) v =
        (a.app (Opposite.op ⦋0⦌) w).val at hh
      rw [hh]
      exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex (a.app (Opposite.op ⦋0⦌) w)
    let g := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift IsZeroFrameVertex (curry F) hv
    have hg : g ≫ ι = curry F := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι _ _ _
    refine CommSq.HasLift.mk' { l := g, fac_left := ?_, fac_right := ?_ }
    · apply (cancel_mono ι).1
      rw [Category.assoc, hg, hc]
    · change g ≫ ι ≫ (pre (framePositiveRow n).ι).app C = b
      rw [← Category.assoc, hg]
      apply uncurry_injective
      rw [uncurry_pre_app, uncurry_curry]
      exact hFG

end SerrePositivity.KST.SConstruction
