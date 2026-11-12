module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.ResolutionFaces

/-!
概要：頂点集合で定めた面上の解像の射影とその同値性。
方針：最大元の射影を面へ制限し、非空な面の順序同型で標準単体上の同値へ移す。
規約：射影自体は面の列挙に依存しない。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW）、交わりを含む面の射影の貼り合わせ。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：等しい部分複体の間の型の移送は包含と整合する。
方針：部分複体の等号を消去する。
規約：等号は underlying 単体集合へ写して用いる。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW）、面を像の計算から同定する際の包含の整理。 -/
lemma subcomplex_eqToHom_ι {X : SSet.{u}} {A B : X.Subcomplex} (h : A = B) :
    eqToHom (congrArg (fun K : X.Subcomplex ↦ K.toSSet) h) ≫ B.ι = A.ι := by
  subst B
  simp

/-- 概要：面の解像の同型は大きい解像への包含と可換。
方針：像への同型の分解式と、部分複体の等号の移送の可換性を使う。
規約：頂点集合 T の順序同型で作った小さい解像からの射。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW）、面上の射影と標準単体上の射影の比較。 -/
lemma coherentResolutionFaceIso_hom_ι {n m : ℕ} (T : Finset (Fin (n + 1)))
    (e : Fin (m + 1) ≃o T) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionFaceIso.{u} T e).hom ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionFace T).ι =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionMap ((OrderHom.Subtype.val (· ∈ T)).comp e.toOrderEmbedding.toOrderHom) := by
  let β := (OrderHom.Subtype.val (· ∈ T)).comp e.toOrderEmbedding.toOrderHom
  change (Subcomplex.toRange (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionMap β) ≫
    eqToHom (congrArg (fun A : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionSimplex.{u} n).Subcomplex ↦ A.toSSet)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.range_coherentResolutionMap_of_orderIso T e))) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionFace T).ι = _
  rw [Category.assoc, subcomplex_eqToHom_ι (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.range_coherentResolutionMap_of_orderIso T e),
    Subcomplex.toRange_ι]

/-- 概要：最大元の射影を指定した面へ制限する。
方針：各段の最大元は旗の台に属するので、射影の単体も同じ頂点集合内にある。
規約：面の頂点集合 T は空でもよい。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW）、面どうしの交わりの上でも自然な射影。 -/
def coherentResolutionFaceProjection {n : ℕ} (T : Finset (Fin (n + 1))) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionFace.{u} T).toSSet ⟶ (stdSimplex.face T).toSSet :=
  Subcomplex.lift ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionFace T).ι ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionProjection n) (by
    intro d σ hσ
    obtain ⟨F, rfl⟩ := hσ
    change Finset.univ.image F.val.down.maxAt ⊆ T
    intro k hk
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hk
    exact F.property (F.val.down.sets_subset_support j (F.val.down.maxAt_mem j)))

/-- 概要：面の射影は大きい単体の射影の制限。
方針：各単体で部分型の値を取る。
規約：部分複体の包含を後に合成する式。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW）、面の射影の貼り合わせの可換性。 -/
lemma coherentResolutionFaceProjection_ι {n : ℕ} (T : Finset (Fin (n + 1))) :
    coherentResolutionFaceProjection.{u} T ≫ (stdSimplex.face T).ι =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionFace T).ι ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionProjection n := rfl

/-- 概要：面の射影を面の順序同型で移すと小さい標準単体上の射影。
方針：両辺を面の包含の後で比較し、射影の自然性を使う。
規約：標的の面の同型は標準単体の表現可能性による同型。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW）、面上の射影の同値性の移送。 -/
lemma coherentResolutionFaceProjection_faceIso {n m : ℕ} (T : Finset (Fin (n + 1)))
    (e : Fin (m + 1) ≃o T) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionFaceIso.{u} T e).hom ≫ coherentResolutionFaceProjection T =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionProjection m ≫
        (stdSimplex.isoOfRepresentableBy (stdSimplex.faceRepresentableBy T m e)).hom := by
  apply (cancel_mono (stdSimplex.face T).ι).mp
  rw [Category.assoc, coherentResolutionFaceProjection_ι, ← Category.assoc,
    coherentResolutionFaceIso_hom_ι]
  have hs : (stdSimplex.isoOfRepresentableBy (stdSimplex.faceRepresentableBy T m e)).hom ≫
      (stdSimplex.face.{u} T).ι = SSet.stdSimplex.map (SimplexCategory.mkHom
        ((OrderHom.Subtype.val (· ∈ T)).comp e.toOrderEmbedding.toOrderHom)) := rfl
  rw [Category.assoc, hs]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionProjectionNat.naturality (SimplexCategory.mkHom
    ((OrderHom.Subtype.val (· ∈ T)).comp e.toOrderEmbedding.toOrderHom))

/-- 概要：順序同型で表示した非空な面上の射影は前合成による同値。
方針：始域と標的の面の同型を使って標準単体上の射影の同値性を移す。
規約：頂点集合の順序同型を明示的に受け取る。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW）、交わりを含む面の射影の同値性。 -/
lemma coherentResolutionFaceProjection_isPrecompositionEquivalence_of_orderIso {n m : ℕ}
    (T : Finset (Fin (n + 1))) (e : Fin (m + 1) ≃o T) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (coherentResolutionFaceProjection.{u} T) := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionFaceIso T e)).cancel_left
  rw [coherentResolutionFaceProjection_faceIso]
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionProjection_isPrecompositionEquivalence m).comp
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso
      (stdSimplex.isoOfRepresentableBy (stdSimplex.faceRepresentableBy T m e)))

/-- 概要：任意の非空な頂点集合の面上の射影は前合成による同値。
方針：有限の頂点集合を順に列挙して順序同型で表示する。
規約：列挙の選択は同値性の命題には現れない。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW）、有限個の面の貼り合わせへの入力。 -/
lemma coherentResolutionFaceProjection_isPrecompositionEquivalence_of_nonempty {n : ℕ}
    (T : Finset (Fin (n + 1))) (hT : T.Nonempty) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (coherentResolutionFaceProjection.{u} T) := by
  have hc : T.card = (T.card - 1) + 1 := by
    have hp := Finset.card_pos.mpr hT
    omega
  exact coherentResolutionFaceProjection_isPrecompositionEquivalence_of_orderIso
    T (T.orderIsoOfFin hc)

/-- 概要：空の面も含めて全ての面上の射影は前合成による同値。
方針：非空の場合は列挙を使い、空の場合は両側の始対象性を使う。
規約：頂点集合について追加条件を課さない。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW）、面の交わりが空の場合も含む貼り合わせ。 -/
lemma coherentResolutionFaceProjection_isPrecompositionEquivalence {n : ℕ}
    (T : Finset (Fin (n + 1))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (coherentResolutionFaceProjection.{u} T) := by
  classical
  by_cases hT : T.Nonempty
  · exact coherentResolutionFaceProjection_isPrecompositionEquivalence_of_nonempty T hT
  · have hT0 : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hT
    subst T
    have hX : CategoryTheory.Limits.IsInitial
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionFace.{u} (∅ : Finset (Fin (n + 1)))).toSSet := by
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionFace_empty]
      exact Subcomplex.isInitialBot
    have hY : CategoryTheory.Limits.IsInitial
        (stdSimplex.face.{u} (∅ : Finset (Fin (n + 1)))).toSSet := by
      rw [stdSimplex.face_empty]
      exact Subcomplex.isInitialBot
    let e := hX.uniqueUpToIso hY
    have he : e.hom = coherentResolutionFaceProjection ∅ := hX.hom_ext _ _
    rw [← he]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso e

/-- 概要：面上の射影は頂点集合の包含と可換。
方針：包含の後で比較すると両側は同じ最大元の射影。
規約：二つの面は同じ標準単体の中にある。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW）、各面の射影を貼り合わせる可換図式。 -/
lemma coherentResolutionFaceProjection_naturality {n : ℕ}
    {T U : Finset (Fin (n + 1))} (h : T ⊆ U) :
    Subcomplex.homOfLE (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionFace_mono.{u} h) ≫ coherentResolutionFaceProjection U =
      coherentResolutionFaceProjection T ≫
        Subcomplex.homOfLE ((stdSimplex.face_le_face_iff T U).mpr h) := by
  apply (cancel_mono (stdSimplex.face U).ι).mp
  rw [Category.assoc, coherentResolutionFaceProjection_ι]
  rfl

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
