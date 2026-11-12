module
public import SerrePositivity.KST.Fibration.WeakStringConstantPullback
public import SerrePositivity.KST.Fibration.WeakStringKernelDiagonalContraction
public import SerrePositivity.KST.Fibration.RelativeSKernelBasepoint
public import SerrePositivity.KST.Fibration.ContractibleBaseFiberComparison

/-!
概要：加法性から得た実 W 列四角形を、指定基点上の相対 fiber へ接続する。
方針：既存の全正反復の homotopy pullback に可縮基底の fiber 比較を適用する。
規約：全正反復では核側の可縮性を明示入力とする。単回版だけは入力なしで証明する。
使われ方：K-6 b の実現に残る入力を特定し、元の包含射を保つ公開界面。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.SConstruction
open SerrePositivity.KST.Comparison
open SerrePositivity.SimplicialModel
namespace SerrePositivity.KST.Fibration.Relative

/-- 概要：W 列と正反復 S の元の同時実現。方針：既存図式の対角を取る。
規約：零回を含めない。使われ方：相対 fiber の底。 -/
def iteratedRelativeSpace {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) (r : ℕ) : SSet.{u} :=
  simplicialDiagonalFunctor.obj (weakStringMultiRealization q (r + 1))

/-- 概要：元の定数 W 列への実包含。方針：既存の定数対角射を使う。
規約：射を選び直さない。使われ方：相対 fiber の元の射。 -/
def iteratedRelativeInclusion {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) (r : ℕ) :
    (multiRealizationFunctor (r + 1)).obj (sInputModel B) ⟶ iteratedRelativeSpace q r :=
  weakStringRealizationConstantDiagonal (multiRealizationFunctor (r + 1)) q

/-- 概要：指定した同じ核基点上の実 fiber。方針：元の包含と後合成を使用する。
規約：基点を明示する。使われ方：全正反復の fiber 比較の値域。 -/
def additivityFiber {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B) (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C)
    (r : ℕ) (z : Δ[0] ⟶ iteratedRelativeSpace (i ≫ q : A ⟶ C) r) : SSet.{u} :=
  homotopyPullbackObject (iteratedRelativeInclusion q r)
    (z ≫ simplicialDiagonalFunctor.map (weakStringMultiPostcomp i q (r + 1)))

/-- 概要：核側可縮性から得る、元の正反復実現と実 fiber の比較。
方針：加法性の四角形に可縮基底比較を適用。規約：可縮性は未解消入力。
使われ方：K-6 b の残る全正反復入力を明示する。 -/
def additivityFiberIsoOfKernelContractible
    {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C}
    (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q) (r : ℕ)
    (hc : IsIso (AnodyneHomotopy.anodyneQ.map
      (terminal.from (iteratedRelativeSpace (i ≫ q : A ⟶ C) r))))
    (z : Δ[0] ⟶ iteratedRelativeSpace (i ≫ q : A ⟶ C) r) :
    AnodyneHomotopy.anodyneQ.obj ((multiRealizationFunctor (r + 1)).obj (sInputModel A)) ≅
      AnodyneHomotopy.anodyneQ.obj (additivityFiber i q r z) :=
  contractibleBaseFiberIso (weakStringConstantPostSquare i q (r + 1)).flip
    ((isHomotopyPullback_flip_iff _).mpr (weakStringConstantPostSquare_homotopyPullback h r))
    hc z

/-- 概要：同じ fiber 比較は元の包含の反復実現を回収する。
方針：可縮基底比較の射影公式。規約：同じ基点・射影を保持。
使われ方：単なる対象別同型と区別した接続。 -/
theorem additivityFiberIsoOfKernelContractible_projection
    {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C}
    (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q) (r : ℕ)
    (hc : IsIso (AnodyneHomotopy.anodyneQ.map
      (terminal.from (iteratedRelativeSpace (i ≫ q : A ⟶ C) r))))
    (z : Δ[0] ⟶ iteratedRelativeSpace (i ≫ q : A ⟶ C) r) :
    (additivityFiberIsoOfKernelContractible h r hc z).hom ≫
      AnodyneHomotopy.anodyneQ.map (pullback.fst _ _) =
        AnodyneHomotopy.anodyneQ.map
          ((multiRealizationFunctor (r + 1)).map (sInputExactMap i)) :=
  contractibleBaseFiberIso_hom_fst (weakStringConstantPostSquare i q (r + 1)).flip
    ((isHomotopyPullback_flip_iff _).mpr (weakStringConstantPostSquare_homotopyPullback h r))
    hc z

/-- 概要：単回版の同じ核基点。方針：元の相対 S 基点を既存比較で送る。
規約：零対象の元の指定を保持。使われ方：無条件の単回 fiber 比較。 -/
def singleAdditivityBasepoint
    {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C}
    (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q) : Δ[0] ⟶ iteratedRelativeSpace (i ≫ q : A ⟶ C) 0 :=
  relativeSKernelBasepoint h ≫ relativeSWeakStringMultiComparison (i ≫ q : A ⟶ C)

/-- 概要：単回版では追加の可縮性入力なしに実 fiber 同型を得る。
方針：既存の核収縮を全反復界面の r=0 に代入する。
規約：全正反復の完成とは数えない。使われ方：既存相対 S との接続の検証。 -/
def singleAdditivityFiberIso
    {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C}
    (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q) :
    AnodyneHomotopy.anodyneQ.obj ((multiRealizationFunctor 1).obj (sInputModel A)) ≅
      AnodyneHomotopy.anodyneQ.obj (additivityFiber i q 0 (singleAdditivityBasepoint h)) :=
  additivityFiberIsoOfKernelContractible h 0
    (weakStringKernelDiagonal_toPoint_localized_isIso h) (singleAdditivityBasepoint h)

/-- 概要：単回の実 fiber 同型の射影は元の包含の実現射そのもの。
方針：一般の射影公式へ既存の単回核収縮を代入する。
規約：同じ実 fiber・基点を保持。使われ方：K-6 b の両射を保つ fiber 列。 -/
theorem singleAdditivityFiberIso_projection
    {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C}
    (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q) :
    (singleAdditivityFiberIso h).hom ≫ AnodyneHomotopy.anodyneQ.map (pullback.fst _ _) =
      AnodyneHomotopy.anodyneQ.map ((multiRealizationFunctor 1).map (sInputExactMap i)) :=
  additivityFiberIsoOfKernelContractible_projection h 0
    (weakStringKernelDiagonal_toPoint_localized_isIso h) (singleAdditivityBasepoint h)

end SerrePositivity.KST.Fibration.Relative
