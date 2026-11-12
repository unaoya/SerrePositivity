module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.ComplexUnitHomIso
public import SerrePositivity.DifferentialGraded.Category.ObjectImage
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.PinchedChainMapComposition

/-! # 任意複体の単位 Hom による実 pinched 模型

概要：任意複体を、任意に指定した対象宇宙の二対象 dg 圏の Hom として実現する。
方針：単位と元の複体を対象ラベルとして引き戻し、実 Hom の pinched 空間を使う。
規約：対象宇宙を拡大しない。使われ方：一般準同型の全射 span による比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory MonoidalCategory DifferentialGraded CochainComplex
variable {A : Type u} [CommRing A]

/-- 単位と任意複体を対象とする、指定宇宙の dg 充満像。 -/
abbrev DGComplexPinchedModel (K : Complex A) :=
  _root_.SerrePositivity.InfinityCategories.DGObjectImage (fun b : ULift.{v} Bool => if b.down then K else 𝟙_ (Complex A))

/-- 単位複体の対象ラベル。 -/
def complexPinchedSource (K : Complex A) : DGComplexPinchedModel.{u, v} K :=
  ⟨ULift.up false⟩

/-- 元の複体の対象ラベル。 -/
def complexPinchedTarget (K : Complex A) : DGComplexPinchedModel.{u, v} K :=
  ⟨ULift.up true⟩

/-- 単位 Hom の実 pinched 写像空間として任意複体を実現する。 -/
abbrev complexPinchedSpace (K : Complex A) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A (DGComplexPinchedModel.{u, v} K)
    (complexPinchedSource K) (complexPinchedTarget K)

/-- 任意の鎖写像による単位 Hom の実 pinched 写像。 -/
def complexPinchedMap {K L : Complex A} (φ : K ⟶ L) :
    complexPinchedSpace.{u, v} K ⟶ complexPinchedSpace.{u, v} L :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap (homPostcompose (𝟙_ (Complex A)) φ)

/-- 恒等鎖写像は実 pinched 模型の恒等写像を誘導する。 -/
lemma complexPinchedMap_id (K : Complex A) :
    complexPinchedMap.{u, v} (𝟙 K) = 𝟙 (complexPinchedSpace.{u, v} K) := by
  have he : homPostcompose (𝟙_ (Complex A)) (𝟙 K) = 𝟙 _ :=
    (homFunctor (𝟙_ (Complex A))).map_id K
  rw [complexPinchedMap, he]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap_id (D := DGComplexPinchedModel.{u, v} K)
    (x := complexPinchedSource K) (y := complexPinchedTarget K)

/-- 鎖写像の合成と実 pinched 模型の写像の合成は一致する。 -/
lemma complexPinchedMap_comp {K L M : Complex A} (φ : K ⟶ L) (ψ : L ⟶ M) :
    complexPinchedMap.{u, v} (φ ≫ ψ) = complexPinchedMap φ ≫ complexPinchedMap ψ := by
  have he : homPostcompose (𝟙_ (Complex A)) (φ ≫ ψ) =
      homPostcompose (𝟙_ (Complex A)) φ ≫ homPostcompose (𝟙_ (Complex A)) ψ :=
    (homFunctor (𝟙_ (Complex A))).map_comp φ ψ
  dsimp only [complexPinchedMap]
  rw [he]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap_comp
    (D := DGComplexPinchedModel.{u, v} K) (E := DGComplexPinchedModel.{u, v} L)
    (T := DGComplexPinchedModel.{u, v} M)
    (x := complexPinchedSource K) (y := complexPinchedTarget K)
    (x' := complexPinchedSource L) (y' := complexPinchedTarget L)
    (x'' := complexPinchedSource M) (y'' := complexPinchedTarget M) _ _

end SerrePositivity.InfinityCategories.Project.DerivedCategories
