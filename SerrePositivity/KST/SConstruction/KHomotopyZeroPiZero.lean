module
public import SerrePositivity.KST.SConstruction.KHomotopyStageIso

/-! # π₀ K と元の K 空間の連結成分の自然な比較
概要：実際の整数次数の零次 K 群と、元の境界商 K 空間の連結成分を自然に同定する。
方針：零段の自然な表示と Kan の零次ホモトピー類の π₀ 比較を合成する。
規約：群構造と三角圏 K₀ の同定は後続。使われ方：対象類と cofiber 関係の自然な比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open Spectra

/-- 元の境界商 K 空間の連結成分の関手。 -/
def boundaryKPiZeroFunctor : StableModel.{u} ⥤ Type u :=
  boundaryKSpaceFunctor ⋙ PointedSimplicialSet.forget ⋙ SSet.π₀Functor

/-- 元の K 空間の零次ホモトピー類と連結成分の自然同型。 -/
def rawKZeroHomotopyPiZeroIso : rawKStageHomotopyFunctor.{u} 0 0 ≅ boundaryKPiZeroFunctor :=
  NatIso.ofComponents (fun _ => _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyZero.equivPiZero.toIso) (fun {X Y} f => by
    apply ConcreteCategory.hom_ext
    intro a
    change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyZero.equivPiZero (pointedHomotopyMap 0 (boundaryKSpaceFunctor.map f) a) =
      SSet.mapπ₀ (boundaryKSpaceFunctor.map f).right (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyZero.equivPiZero a)
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyZero.equivPiZero_map _ _ a)

/-- 実際の BF K スペクトルの零次群の基礎集合は元の K 空間の π₀ と自然同型。 -/
def kHomotopyZeroPiZeroIso :
    kHomotopyFunctor.{u} 0 ⋙ forget CommGrpCat.{u} ≅ boundaryKPiZeroFunctor :=
  kHomotopyRawStageIso 0 0 (by omega) ≪≫ rawKZeroHomotopyPiZeroIso

/-- 零次 K 群と元の K 空間の π₀ の自然同型の各成分を集合の同値として使う。 -/
def kHomotopyZeroPiZeroEquiv (X : StableModel.{u}) :
    OmegaSpectrum.homotopyGroup (kOmegaSpectrum X) 0 ≃
      SSet.π₀ (boundaryKSpaceFunctor.obj X).right :=
  (kHomotopyZeroPiZeroIso.{u}.app X).toEquiv

end SerrePositivity.KST.SConstruction
