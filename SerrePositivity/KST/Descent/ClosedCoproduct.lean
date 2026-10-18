module

public import SerrePositivity.KST.Descent.SectionOrbit

/-!
# 被約な終域の互いに素な有限閉被覆

## 概要
被約スキームを互いに素な閉埋め込みで有限被覆すると、非交和からの射が同型になる。

## 方針
各像の補集合を残りの有限個の閉像の和と書き、各閉像が開でもあることを示す。
被約性から閉埋め込みをその開像との同型にし、非交和の開埋め込み性を適用する。

## 規約
点集合の全単射だけから同型を結論しない。
各射の閉埋め込み性と、終域の被約性を用いる。

## 使われ方
論文 定理 3.1 の軌道射が一致中心の外で同型であることの幾何学的な入力。
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

namespace SerrePositivity.KST.Descent

/-- 概要：被約な終域への開像を持つ閉埋め込みは開埋め込み（論文 定理 3.1）。
方針：その開像への持ち上げを全射閉埋め込みにし、被約性から同型にする。
規約：開像だけでなく終域の被約性を仮定する。
使われ方：互いに素な有限閉被覆を非交和の分解に移す。 -/
theorem openImmersion_of_closedImmersion_of_open_range {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsClosedImmersion f] [IsReduced Y]
    (open_range : IsOpen (Set.range f)) : IsOpenImmersion f := by
  let U : Y.Opens := ⟨Set.range f, open_range⟩
  have range_inclusion : Set.range U.ι = Set.range f := by simp [U]
  let lift := IsOpenImmersion.lift U.ι f (by rw [range_inclusion])
  have fac : lift ≫ U.ι = f := IsOpenImmersion.lift_fac _ _ _
  have : IsClosedImmersion (lift ≫ U.ι) := by rw [fac]; infer_instance
  have : IsClosedImmersion lift := IsClosedImmersion.of_comp lift U.ι
  have : Surjective lift := by
    constructor
    intro y
    obtain ⟨x, hx⟩ : ∃ x, f x = U.ι y := y.property
    refine ⟨x, U.ι.isOpenEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, fac]
    exact hx
  have : IsIso lift := isIso_of_surjective_closedImmersion lift
  rw [← fac]
  infer_instance

/-- 概要：有限の互いに素な閉被覆の各像は開（論文 定理 3.1）。
方針：各像の補集合を、それ以外の像の有限和と同定する。
規約：各像の閉性・互いに素・全体を覆うことを明示する。
使われ方：有限閉被覆を開被覆として扱う。 -/
theorem open_range_of_finite_disjoint_closed_cover {I : Type u} [Finite I]
    {Y : I → Scheme.{u}} {X : Scheme.{u}} (f : ∀ i, Y i ⟶ X)
    [∀ i, IsClosedImmersion (f i)]
    (disjoint : Pairwise fun i j ↦ Disjoint (Set.range (f i)) (Set.range (f j)))
    (covering : ⋃ i, Set.range (f i) = Set.univ) (i : I) : IsOpen (Set.range (f i)) := by
  classical
  have complement : Set.range (f i) = (⋃ j : {j : I // j ≠ i}, Set.range (f j.val))ᶜ := by
    ext x
    constructor
    · intro hx hxrest
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hxrest
      exact Set.disjoint_left.mp (disjoint j.property.symm) hx hj
    · intro hx
      have hxcover : x ∈ ⋃ j, Set.range (f j) := by rw [covering]; exact Set.mem_univ x
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hxcover
      by_cases eq : j = i
      · subst j
        exact hj
      · exact False.elim (hx (Set.mem_iUnion.mpr ⟨⟨j, eq⟩, hj⟩))
  rw [complement]
  have closed : IsClosed (⋃ j : {j : I // j ≠ i}, Set.range (f j.val)) :=
    isClosed_iUnion_of_finite fun j ↦ (f j.val).isClosedEmbedding.isClosed_range
  exact closed.isOpen_compl

/-- 概要：被約スキームの互いに素な有限閉被覆は非交和の同型（論文 定理 3.1）。
方針：各閉射を開射とし、非交和からの開埋め込みの全射性で同型にする。
規約：非被約な終域に対しては主張しない。
使われ方：軌道正方形の中心の補集合上での同型性。 -/
theorem finiteClosedCoproduct_isIso {I : Type u} [Finite I]
    {Y : I → Scheme.{u}} {X : Scheme.{u}} [IsReduced X] (f : ∀ i, Y i ⟶ X)
    [∀ i, IsClosedImmersion (f i)]
    (disjoint : Pairwise fun i j ↦ Disjoint (Set.range (f i)) (Set.range (f j)))
    (covering : ⋃ i, Set.range (f i) = Set.univ) : IsIso (Sigma.desc f) := by
  have (i : I) : IsOpenImmersion (f i) :=
    openImmersion_of_closedImmersion_of_open_range (f i)
      (open_range_of_finite_disjoint_closed_cover f disjoint covering i)
  have : IsOpenImmersion (Sigma.desc f) := isOpenImmersion_sigmaDesc Y f disjoint
  have : Surjective (Sigma.desc f) := Surjective.sigmaDesc_of_union_range_eq_univ covering
  apply isIso_of_isOpenImmersion_of_opensRange_eq_top
  apply Opens.ext
  exact range_eq_univ (Sigma.desc f)

end SerrePositivity.KST.Descent
