module
public import SerrePositivity.KST.SConstruction.ComonoidTriplePair
public import SerrePositivity.KST.SConstruction.CubicalLambdaTensorNaturality
public import SerrePositivity.KST.SConstruction.DGTensorAssociator

/-! # 元の Λ の三つの出力への実 dg 関手
概要：同じ元の Serre 対角で三つの入力作用を束ね、元の結合関手との両立を証明する。
方針：全 Hom 上で元の余モノイドの三出力の計算と入力合成の回収式を使う。
規約：対象と全 Hom の三出力を保持。使われ方：Λ の実 oplax tensor の結合則。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory Simplicial SSet
open SerrePositivity.DifferentialGraded
open scoped ComonObj
variable (A : Type u) [CommRing A]

/-- 元の三入力作用を、左から二つずつ束ねる実 dg 関手。 -/
def cubicalLambdaTripleLeft {M K L N : SSet.{u}} (a : M ⟶ K) (b : M ⟶ L) (c : M ⟶ N) :
    DGFunctor A (CubicalLambda A M)
      (DGTensorCategory A (DGTensorCategory A (CubicalLambda A K) (CubicalLambda A L))
        (CubicalLambda A N)) :=
  DGFunctor.comp (cubicalLambdaDiagonal A M)
    (dgTensorFunctor A (cubicalLambdaTensorPair A a b) (cubicalLambdaMap A c))

/-- 元の三入力作用を、右から二つずつ束ねる実 dg 関手。 -/
def cubicalLambdaTripleRight {M K L N : SSet.{u}} (a : M ⟶ K) (b : M ⟶ L) (c : M ⟶ N) :
    DGFunctor A (CubicalLambda A M)
      (DGTensorCategory A (CubicalLambda A K)
        (DGTensorCategory A (CubicalLambda A L) (CubicalLambda A N))) :=
  DGFunctor.comp (cubicalLambdaDiagonal A M)
    (dgTensorFunctor A (cubicalLambdaMap A a) (cubicalLambdaTensorPair A b c))

/-- 元の三つの入力作用を束ねる左右の実 dg 関手は、元の結合関手を介して一致する。 -/
lemma cubicalLambdaTriplePair_associativity {M K L N : SSet.{u}}
    (a : M ⟶ K) (b : M ⟶ L) (c : M ⟶ N) :
    DGFunctor.comp (cubicalLambdaTripleLeft A a b c)
        (dgTensorAssociator A (CubicalLambda A K) (CubicalLambda A L) (CubicalLambda A N)) =
      cubicalLambdaTripleRight A a b c := by
  refine EnrichedFunctor.ext (Complex A)
    (F := DGFunctor.comp (cubicalLambdaTripleLeft A a b c)
      (dgTensorAssociator A (CubicalLambda A K) (CubicalLambda A L) (CubicalLambda A N)))
    (G := cubicalLambdaTripleRight A a b c) (fun _ => rfl) ?_
  intro x y
  exact (Category.comp_id _).trans (comonoidTriplePair (cubicalLambdaHomComonoid A M x y)
    ((cubicalLambdaMap A a).map x y) ((cubicalLambdaMap A b).map x y)
    ((cubicalLambdaMap A c).map x y))

/-- 第一出力を二つに分ける実 dg 関手は、元の入力の二つの合成を回収する。 -/
lemma cubicalLambdaTensorPair_split_left {M K L X Y : SSet.{u}}
    (a : M ⟶ K) (b : M ⟶ L) (f : K ⟶ X) (g : K ⟶ Y) :
    DGFunctor.comp (cubicalLambdaTensorPair A a b)
        (dgTensorFunctor A (cubicalLambdaTensorPair A f g) (DGFunctor.id (CubicalLambda A L))) =
      cubicalLambdaTripleLeft A (a ≫ f) (a ≫ g) b := by
  refine EnrichedFunctor.ext (Complex A)
    (F := DGFunctor.comp (cubicalLambdaTensorPair A a b)
      (dgTensorFunctor A (cubicalLambdaTensorPair A f g) (DGFunctor.id (CubicalLambda A L))))
    (G := cubicalLambdaTripleLeft A (a ≫ f) (a ≫ g) b) (fun _ => rfl) ?_
  intro x y
  have ht := comonoidPair_split_left (cubicalLambdaMapComonoid A a x y)
    ((cubicalLambdaMap A b).map x y)
    ((cubicalLambdaMap A f).map ((cubicalLambdaMap A a).obj x) ((cubicalLambdaMap A a).obj y))
    ((cubicalLambdaMap A g).map ((cubicalLambdaMap A a).obj x) ((cubicalLambdaMap A a).obj y))
  have hs := congrArg₂ (fun p q => p ⊗ₘ q)
    (cubicalLambdaMap_comp_map A a f x y).symm (cubicalLambdaMap_comp_map A a g x y).symm
  exact (Category.comp_id _).trans (ht.trans
    (congrArg (fun p => Δ[x ⟶[Complex A] y] ≫
      ((Δ[x ⟶[Complex A] y] ≫ p) ⊗ₘ (cubicalLambdaMap A b).map x y)) hs))

/-- 第二出力を二つに分ける実 dg 関手は、元の入力の二つの合成を回収する。 -/
lemma cubicalLambdaTensorPair_split_right {M K L X Y : SSet.{u}}
    (a : M ⟶ K) (b : M ⟶ L) (f : L ⟶ X) (g : L ⟶ Y) :
    DGFunctor.comp (cubicalLambdaTensorPair A a b)
        (dgTensorFunctor A (DGFunctor.id (CubicalLambda A K)) (cubicalLambdaTensorPair A f g)) =
      cubicalLambdaTripleRight A a (b ≫ f) (b ≫ g) := by
  refine EnrichedFunctor.ext (Complex A)
    (F := DGFunctor.comp (cubicalLambdaTensorPair A a b)
      (dgTensorFunctor A (DGFunctor.id (CubicalLambda A K)) (cubicalLambdaTensorPair A f g)))
    (G := cubicalLambdaTripleRight A a (b ≫ f) (b ≫ g)) (fun _ => rfl) ?_
  intro x y
  have ht := comonoidPair_split_right ((cubicalLambdaMap A a).map x y)
    (cubicalLambdaMapComonoid A b x y)
    ((cubicalLambdaMap A f).map ((cubicalLambdaMap A b).obj x) ((cubicalLambdaMap A b).obj y))
    ((cubicalLambdaMap A g).map ((cubicalLambdaMap A b).obj x) ((cubicalLambdaMap A b).obj y))
  have hs := congrArg₂ (fun p q => p ⊗ₘ q)
    (cubicalLambdaMap_comp_map A b f x y).symm (cubicalLambdaMap_comp_map A b g x y).symm
  exact (Category.comp_id _).trans (ht.trans
    (congrArg (fun p => Δ[x ⟶[Complex A] y] ≫
      ((cubicalLambdaMap A a).map x y ⊗ₘ (Δ[x ⟶[Complex A] y] ≫ p))) hs))

/-- 元の三つの入力作用を束ねる実 dg 関手は、元の全前合成を厳密に保つ。 -/
lemma cubicalLambdaTripleRight_precompose {M' M K L N : SSet.{u}}
    (h : M' ⟶ M) (a : M ⟶ K) (b : M ⟶ L) (c : M ⟶ N) :
    DGFunctor.comp (cubicalLambdaMap A h) (cubicalLambdaTripleRight A a b c) =
      cubicalLambdaTripleRight A (h ≫ a) (h ≫ b) (h ≫ c) := by
  refine EnrichedFunctor.ext (Complex A)
    (F := DGFunctor.comp (cubicalLambdaMap A h) (cubicalLambdaTripleRight A a b c))
    (G := cubicalLambdaTripleRight A (h ≫ a) (h ≫ b) (h ≫ c)) (fun _ => rfl) ?_
  intro x y
  have ht := comonoidTripleRight_precompose (cubicalLambdaMapComonoid A h x y)
    ((cubicalLambdaMap A a).map ((cubicalLambdaMap A h).obj x) ((cubicalLambdaMap A h).obj y))
    ((cubicalLambdaMap A b).map ((cubicalLambdaMap A h).obj x) ((cubicalLambdaMap A h).obj y))
    ((cubicalLambdaMap A c).map ((cubicalLambdaMap A h).obj x) ((cubicalLambdaMap A h).obj y))
  have hs := congrArg₂ (fun p q => p ⊗ₘ q)
    (cubicalLambdaMap_comp_map A h b x y).symm (cubicalLambdaMap_comp_map A h c x y).symm
  have hu := congrArg₂ (fun p q => p ⊗ₘ (Δ[x ⟶[Complex A] y] ≫ q))
    (cubicalLambdaMap_comp_map A h a x y).symm hs
  exact (Category.comp_id _).trans
    (ht.trans (congrArg (fun p => Δ[x ⟶[Complex A] y] ≫ p) hu))

end SerrePositivity.KST.SConstruction
