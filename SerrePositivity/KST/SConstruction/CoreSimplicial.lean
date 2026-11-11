module
public import SerrePositivity.KST.SConstruction.FirstRowFibration
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CoreKan
public import Mathlib.CategoryTheory.Functor.Currying

/-! # S• の単体的 Kan core と対角
概要：各 gapped 図式圏の core を取り、単体的 Kan 複体とその対角を構成する。
方針：α2 の core 関手と S• の合成を用い、二つの単体次数を対角で同時に制限する。
規約：BGT §7、Kerodon 4.4.3（Tag 01CZ）。Kan 性を対角に直接主張せず、後で Kan 置換する。
使われ方：連結 K 空間の対角実現模型。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：S_n C の可逆な辺からなる core。
方針：α2 の quasicategoryCore を適用する。
規約：全 gapped 図式を保持する。使われ方：単体的 Kan 複体の各段。 -/
def coreSConstruction (n : ℕ) (C : SSet.{u}) : SSet.{u} :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (sConstruction n C) : SSet.{u})

/-- 概要：C が quasicategory なら S_n C の core は Kan 複体。
方針：gapped 図式圏の quasicategory 性と α2 の core の Kan 性を使う。
規約：C の安定性は不要。使われ方：実現前の各段の Kan 性。 -/
instance coreSConstruction_kanComplex (n : ℕ) (C : SSet.{u}) [Quasicategory C] :
    KanComplex (coreSConstruction n C) := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.quasicategoryCore_kanComplex _

/-- 概要：単調写像による S• の前合成を core の射へ送る。
方針：core の関手性を使う。
規約：反変の向き。使われ方：単体的 core の面・退化作用。 -/
def coreSMap {m n : ℕ} (C : SSet.{u}) (θ : Fin (m + 1) →o Fin (n + 1)) :
    coreSConstruction n C ⟶ coreSConstruction m C := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap (sMap C θ)

/-- 概要：S• の各段で core を取った単体的 Kan 複体。
方針：S• 関手と core 関手を合成する。
規約：値の Kan 性は C が quasicategory のときに成立する。
使われ方：BGT §7 の ιS•C。 -/
def simplicialCoreSConstruction (C : SSet.{u}) : SimplexCategoryᵒᵖ ⥤ SSet.{u} :=
  simplicialSConstruction C ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor

/-- 概要：単体的 core の各段は Kan 複体。
方針：各段の core の Kan 性を使う。
規約：全ての単体次数。使われ方：対角実現の入力。 -/
instance simplicialCoreSConstruction_obj_kanComplex (C : SSet.{u}) [Quasicategory C]
    (n : SimplexCategoryᵒᵖ) : KanComplex ((simplicialCoreSConstruction C).obj n) :=
  coreSConstruction_kanComplex _ C

/-- 概要：零図式の頂点は core に属する。
方針：core が全ての頂点を含むことを使う。
規約：選んだ零対象 z を明示する。使われ方：実現の基点。 -/
def coreSConstructionZeroVertex (n : ℕ) {C : SSet.{u}} [Quasicategory C]
    (z : C _⦋0⦌) (hz : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex z) : (coreSConstruction n C) _⦋0⦌ :=
  ⟨sConstructionZeroVertex n z hz, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore_vertex _⟩

/-- 概要：単体作用は core 内でも零図式の頂点を厳密に保つ。
方針：core の包含後で S• の零頂点の自然性を使う。
規約：頂点の厳密等号。使われ方：単体的な基点の整合性。 -/
lemma coreSMap_zeroVertex {m n : ℕ} {C : SSet.{u}} [Quasicategory C]
    (θ : Fin (m + 1) →o Fin (n + 1)) (z : C _⦋0⦌) (hz : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex z) :
    (coreSMap C θ).app (Opposite.op ⦋0⦌) (coreSConstructionZeroVertex n z hz) =
      coreSConstructionZeroVertex m z hz := by
  apply Subtype.ext
  exact sMap_zeroVertex θ z hz

/-- 概要：単体的 core の対角実現の単体集合模型。
方針：uncurry した二重単体集合を対角関手で制限する。
規約：n 単体は (ιS_n C)_n。Kan 性はここでは課さない。
使われ方：K(C)=Ω|ιS•C| の実現模型。 -/
def diagonalCoreSConstruction (C : SSet.{u}) : SSet.{u} :=
  Functor.diag SimplexCategoryᵒᵖ ⋙ Functor.uncurry.obj (simplicialCoreSConstruction C)

/-- 概要：対角の零単体は S_0 の core の零単体。
方針：対角制限の値の定義を計算する。
規約：厳密等号。使われ方：実現の基点の指定。 -/
lemma diagonalCoreSConstruction_obj (C : SSet.{u}) (n : SimplexCategoryᵒᵖ) :
    (diagonalCoreSConstruction C).obj n = (coreSConstruction n.unop.len C).obj n := rfl

/-- 概要：対角の射は外側の単体作用と内側の単体作用を合成したもの。
方針：uncurry と対角関手の射への作用を計算する。
規約：二つの次数を同じ射で動かす。使われ方：対角実現の構造の照合。 -/
lemma diagonalCoreSConstruction_map (C : SSet.{u}) {d e : SimplexCategoryᵒᵖ}
    (f : d ⟶ e) (x : (diagonalCoreSConstruction C).obj d) :
    (diagonalCoreSConstruction C).map f x =
      ((simplicialCoreSConstruction C).obj e).map f
        (((simplicialCoreSConstruction C).map f).app d x) := rfl

/-- 概要：Kan 複体では全辺が可逆なので core の包含は同型。
方針：Kan の外側ホーン充填で全辺の可逆性を示し、恒等射を core に持ち上げる。
規約：本レーン内の比較同型。使われ方：S_0 の core の可縮性。 -/
def kanCoreIso (X : SSet.{u}) [KanComplex X] : X ≅ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore X : SSet.{u}) where
  hom := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreLift (𝟙 X) (fun s => by
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex s)
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.isInvertibleEdge_of_hasFinalHornFillers _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.hasFinalHornFillers_of_kanComplex _))
  inv := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore X).ι
  hom_inv_id := rfl
  inv_hom_id := by
    apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore X).ι).1
    rfl

/-- 概要：S_0 の core は零対象の選択を全て保つ可縮 Kan 複体。
方針：S_0 の可縮 Kan 性と、Kan 複体とその core の比較同型を使う。
規約：安定性は不要。使われ方：実現の連結性と基点の選択独立性の基礎。 -/
lemma coreSConstructionZero_isContractibleKan (C : SSet.{u}) [Quasicategory C]
    [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.HasZeroVertex C] : _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (coreSConstruction 0 C) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.isContractibleKan_of_iso (kanCoreIso (sConstruction 0 C)) (sConstructionZero_isContractibleKan C)

end SerrePositivity.KST.SConstruction
