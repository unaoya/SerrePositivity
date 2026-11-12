module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.ResolutionBoundary

/-!
概要：標準単体の面の像の上での解像の射影。
方針：単射な頂点写像の始域と像の同型を使い、標準単体上の射影を移す。
規約：像の射影と大きい単体の射影との可換式を明示する。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW）、境界上の射影を面から貼り合わせるための比較。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：単射な頂点写像が与える標準単体の射は単射。
方針：単体圏の単射性を Yoneda 埋め込みで写す。
規約：解像側の対応する単射性と同じ頂点写像を使う。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW）、面の像と小さい標準単体の同型。 -/
lemma stdSimplex_map_mono_of_injective {n m : ℕ}
    (β : Fin (n + 1) →o Fin (m + 1)) (hβ : Function.Injective β) :
    Mono (SSet.stdSimplex.{u}.map (SimplexCategory.mkHom β)) := by
  rw [NatTrans.mono_iff_mono_app]
  intro d
  rw [mono_iff_injective]
  intro s t h
  apply stdSimplex.ext
  intro k
  exact hβ (congrArg (fun r : ULift.{u} (d.unop ⟶ ⦋m⦌) ↦ r.down.toOrderHom k) h)

/-- 概要：解像の面の像から標準単体の面の像への射影。
方針：始域と像の同型で小さい標準単体上の射影を移す。
規約：単射な頂点写像の証明を引数に持つ。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW）、面ごとの射影の構成。 -/
noncomputable def coherentResolutionImageProjection {n m : ℕ}
    (β : Fin (n + 1) →o Fin (m + 1)) (hβ : Function.Injective β) :
    (Subcomplex.range (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionMap.{u} β)).toSSet ⟶
      (Subcomplex.range (SSet.stdSimplex.map (SimplexCategory.mkHom β))).toSSet := by
  haveI := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionMap_mono.{u} β hβ
  haveI := stdSimplex_map_mono_of_injective.{u} β hβ
  exact (asIso (Subcomplex.toRange (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionMap β))).inv ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionProjection n ≫ Subcomplex.toRange (SSet.stdSimplex.map (SimplexCategory.mkHom β))

/-- 概要：面の像の射影を小さい解像から計算する。
方針：像への同型とその逆の合成を消去する。
規約：像への標準の全射を前に合成した式。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW）、面の像の射影の同値性を移す式。 -/
lemma coherentResolutionImageProjection_toRange {n m : ℕ}
    (β : Fin (n + 1) →o Fin (m + 1)) (hβ : Function.Injective β) :
    Subcomplex.toRange (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionMap.{u} β) ≫ coherentResolutionImageProjection β hβ =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionProjection n ≫
        Subcomplex.toRange (SSet.stdSimplex.map (SimplexCategory.mkHom β)) := by
  haveI := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionMap_mono.{u} β hβ
  haveI := stdSimplex_map_mono_of_injective.{u} β hβ
  exact Iso.hom_inv_id_assoc (asIso (Subcomplex.toRange (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionMap β))) _

/-- 概要：面の像の射影は大きい単体の射影と可換。
方針：像への全射を前に合成し、標準単体の図式の射影の自然性を使う。
規約：像の包含を後ろに合成した式。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW）、面から境界への射影の貼り合わせ。 -/
lemma coherentResolutionImageProjection_ι {n m : ℕ}
    (β : Fin (n + 1) →o Fin (m + 1)) (hβ : Function.Injective β) :
    coherentResolutionImageProjection.{u} β hβ ≫
      (Subcomplex.range (SSet.stdSimplex.map (SimplexCategory.mkHom β))).ι =
      (Subcomplex.range (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionMap β)).ι ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionProjection m := by
  apply (cancel_epi (Subcomplex.toRange (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionMap β))).mp
  rw [← Category.assoc, coherentResolutionImageProjection_toRange]
  rw [Category.assoc, Subcomplex.toRange_ι]
  rw [← Category.assoc, Subcomplex.toRange_ι]
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionProjectionNat.naturality (SimplexCategory.mkHom β)).symm

/-- 概要：各面の像の射影は前合成による同値を与える。
方針：両側の像への同型で標準単体上の射影の同値性を移す。
規約：標準単体とその面の像に対する主張。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW）、境界上の射影の貼り合わせの基本例。 -/
lemma coherentResolutionImageProjection_isPrecompositionEquivalence {n m : ℕ}
    (β : Fin (n + 1) →o Fin (m + 1)) (hβ : Function.Injective β) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (coherentResolutionImageProjection.{u} β hβ) := by
  haveI := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionMap_mono.{u} β hβ
  haveI := stdSimplex_map_mono_of_injective.{u} β hβ
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso
    (asIso (Subcomplex.toRange (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionMap β))).symm).comp
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionProjection_isPrecompositionEquivalence n).comp
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso
          (asIso (Subcomplex.toRange (SSet.stdSimplex.map (SimplexCategory.mkHom β))))))

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
