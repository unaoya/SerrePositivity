module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.OverPullbackColimits
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：底の単体ごとに形が変わる関手の族を、底上の単体集合として構成する。
方針：底への標準単体と、その上の図式への射の依存和を取る。
規約：関手 F は通常の Over 圏から単体集合への関手。充填性は定義には含めない。
使われ方：Kerodon Lemma 7.3.4.5（Tag 02ZR） の fiber ごとの関手空間の構成。

対応節は Kerodon 4.5（Tag 01DE）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence

/-- 概要：底へのパラメータ T と、その逆像に対応する図式の関手を束縛する。
方針：構造射 σ と F(σ)→D の依存和。
規約：T が標準単体の場合は族の単体を、一般の T では族の普遍性の入力を表す。
使われ方：底に従って変わる定義域を持つ関手の族。 -/
abbrev FiberwiseFunctorSimplex {B : SSet.{u}} (F : Over B ⥤ SSet.{u})
    (D : SSet.{u}) (T : SSet.{u}) : Type u :=
  Σ σ : T ⟶ B, F.obj (Over.mk σ) ⟶ D

/-- 概要：底単体の前合成に沿って fiber ごとの関手を制限する。
方針：Over 圏の標準射を F で写して前合成する。
規約：制限は面・退化に限らない。
使われ方：fiber ごとの関手の族の全単体的構造。 -/
def fiberwiseFunctorRestrict {B : SSet.{u}} (F : Over B ⥤ SSet.{u})
    (D : SSet.{u}) {T U : SSet.{u}} (α : T ⟶ U)
    (s : FiberwiseFunctorSimplex F D U) : FiberwiseFunctorSimplex F D T :=
  ⟨α ≫ s.1, F.map (Over.homMk α rfl :
    Over.mk (α ≫ s.1) ⟶ Over.mk s.1) ≫ s.2⟩

/-- 概要：fiber ごとの関手の制限は恒等射を保つ。
方針：標準単体・F の恒等則を使う。
規約：底の単体の等式による依存も同時に扱う。
使われ方：族の単体集合の恒等則。 -/
lemma fiberwiseFunctorRestrict_id {B : SSet.{u}} (F : Over B ⥤ SSet.{u})
    (D : SSet.{u}) {T : SSet.{u}} (s : FiberwiseFunctorSimplex F D T) :
    fiberwiseFunctorRestrict F D (𝟙 T) s = s := by
  rcases s with ⟨σ, h⟩
  apply Sigma.ext (Category.id_comp σ)
  apply heq_of_eq
  change F.map (𝟙 (Over.mk σ)) ≫ h = h
  rw [CategoryTheory.Functor.map_id, Category.id_comp]

/-- 概要：fiber ごとの関手の制限は合成を反変に保つ。
方針：Over の射と F の合成則を使う。
規約：任意の面・退化の合成に適用する。
使われ方：族の単体集合の合成則。 -/
lemma fiberwiseFunctorRestrict_comp {B : SSet.{u}} (F : Over B ⥤ SSet.{u})
    (D : SSet.{u}) {T U V : SSet.{u}} (α : T ⟶ U) (β : U ⟶ V)
    (s : FiberwiseFunctorSimplex F D V) :
    fiberwiseFunctorRestrict F D (α ≫ β) s =
      fiberwiseFunctorRestrict F D α (fiberwiseFunctorRestrict F D β s) := by
  rcases s with ⟨σ, h⟩
  apply Sigma.ext (Category.assoc α β σ)
  apply heq_of_eq
  change F.map (Over.homMk (α ≫ β) rfl : Over.mk ((α ≫ β) ≫ σ) ⟶ Over.mk σ) ≫ h =
    F.map (Over.homMk α rfl : Over.mk (α ≫ (β ≫ σ)) ⟶ Over.mk (β ≫ σ)) ≫
      F.map (Over.homMk β rfl : Over.mk (β ≫ σ) ⟶ Over.mk σ) ≫ h
  have he : (Over.homMk (α ≫ β) rfl : Over.mk ((α ≫ β) ≫ σ) ⟶ Over.mk σ) =
      (Over.homMk α rfl : Over.mk (α ≫ (β ≫ σ)) ⟶ Over.mk (β ≫ σ)) ≫
        (Over.homMk β rfl : Over.mk (β ≫ σ) ⟶ Over.mk σ) := by
    apply Over.OverMorphism.ext
    rfl
  rw [he, CategoryTheory.Functor.map_comp]
  exact Category.assoc _ _ _

/-- 概要：底の単体ごとの F 図式を D へ写す関手の全空間。
方針：標準単体上の射の依存和を各次数に置く。
規約：底の単体の宇宙 u を保つ。
使われ方：fiber ごとの普遍余錐の大域的な組み立ての値域。 -/
@[kerodon 046N]
def fiberwiseFunctor {B : SSet.{u}} (F : Over B ⥤ SSet.{u}) (D : SSet.{u}) : SSet.{u} where
  obj n := FiberwiseFunctorSimplex F D (stdSimplex.obj n.unop)
  map α := ↾fiberwiseFunctorRestrict F D (stdSimplex.map α.unop)
  map_id n := by
    apply ConcreteCategory.hom_ext
    intro s
    change fiberwiseFunctorRestrict F D (stdSimplex.map (𝟙 n.unop)) s = s
    rw [CategoryTheory.Functor.map_id]
    exact fiberwiseFunctorRestrict_id F D s
  map_comp α β := by
    apply ConcreteCategory.hom_ext
    intro s
    change fiberwiseFunctorRestrict F D (stdSimplex.map (β.unop ≫ α.unop)) s = _
    rw [CategoryTheory.Functor.map_comp]
    exact fiberwiseFunctorRestrict_comp F D _ _ s

/-- 概要：fiber ごとの関手から底への射影。
方針：依存和の底単体を Yoneda の同値で単体へ戻す。
規約：関手の成分を忘れる。
使われ方：底上の始対象・終対象の持ち上げ問題。 -/
def fiberwiseFunctorProjection {B : SSet.{u}} (F : Over B ⥤ SSet.{u}) (D : SSet.{u}) :
    fiberwiseFunctor F D ⟶ B where
  app n := ↾fun s ↦ SSet.yonedaEquiv s.1
  naturality {m n} α := by
    apply ConcreteCategory.hom_ext
    intro s
    change SSet.yonedaEquiv (stdSimplex.map α.unop ≫ s.1) =
      B.map α (SSet.yonedaEquiv s.1)
    exact (SSet.yonedaEquiv_naturality _ _).symm

/-- 概要：一つの底上の図式から、全ての単体に整合する fiber ごとの関手の族を作る。
方針：各単体への標準射で図式を制限する。
規約：F の余極限保存はこの向きには不要。
使われ方：底上の族と元の図式の普遍性の順方向。 -/
def fiberwiseFunctorCurry {B A D : SSet.{u}} (F : Over B ⥤ SSet.{u})
    (s : FiberwiseFunctorSimplex F D A) : A ⟶ fiberwiseFunctor F D where
  app n := ↾fun x ↦ fiberwiseFunctorRestrict F D (SSet.yonedaEquiv.symm x) s
  naturality {m n} α := by
    apply ConcreteCategory.hom_ext
    intro x
    change fiberwiseFunctorRestrict F D (SSet.yonedaEquiv.symm (A.map α x)) s =
      fiberwiseFunctorRestrict F D (stdSimplex.map α.unop)
        (fiberwiseFunctorRestrict F D (SSet.yonedaEquiv.symm x) s)
    have he : SSet.yonedaEquiv.symm (A.map α x) =
        stdSimplex.map α.unop ≫ SSet.yonedaEquiv.symm x :=
      (SSet.yonedaEquiv_symm_naturality_left α.unop x).symm
    exact (congrArg (fun q ↦ fiberwiseFunctorRestrict F D q s) he).trans
      (fiberwiseFunctorRestrict_comp F D _ _ s)

/-- 概要：組み立てた族の底への射影は元の構造射。
方針：Yoneda の同値の合成則と往復を使う。
規約：厳密な射の等式。
使われ方：局所図式から底上の持ち上げ問題を作る。 -/
lemma fiberwiseFunctorCurry_projection {B A D : SSet.{u}} (F : Over B ⥤ SSet.{u})
    (s : FiberwiseFunctorSimplex F D A) :
    fiberwiseFunctorCurry F s ≫ fiberwiseFunctorProjection F D = s.1 := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro x
  change SSet.yonedaEquiv (SSet.yonedaEquiv.symm x ≫ s.1) = s.1.app n x
  rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]

/-- 概要：標準単体上の図式から作った族の単体は元のデータ。
方針：標準単体の恒等射での評価と制限の単位律を使う。
規約：F に保存性は不要。
使われ方：全空間の各単体の意味を元の図式と厳密に照合する。 -/
lemma fiberwiseFunctorCurry_simplex {B D : SSet.{u}} (F : Over B ⥤ SSet.{u})
    {n : SimplexCategory} (s : FiberwiseFunctorSimplex F D (stdSimplex.obj n)) :
    SSet.yonedaEquiv (fiberwiseFunctorCurry F s) = s := by
  change fiberwiseFunctorRestrict F D
    (SSet.yonedaEquiv.symm (SSet.yonedaEquiv (𝟙 (stdSimplex.obj n)))) s = s
  rw [Equiv.symm_apply_apply]
  exact fiberwiseFunctorRestrict_id F D s

/-- 概要：図式からの族の構成はパラメータの任意の射での制限と可換。
方針：各単体で制限の合成則と Yoneda の自然性を使う。
規約：標準単体に限らないパラメータ変更。
使われ方：骨格・境界・セルの貼り合わせと族の普遍性の整合。 -/
lemma fiberwiseFunctorCurry_precomp {B A A₀ D : SSet.{u}} (F : Over B ⥤ SSet.{u})
    (s : FiberwiseFunctorSimplex F D A) (i : A₀ ⟶ A) :
    fiberwiseFunctorCurry F (fiberwiseFunctorRestrict F D i s) =
      i ≫ fiberwiseFunctorCurry F s := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro x
  change fiberwiseFunctorRestrict F D (SSet.yonedaEquiv.symm x)
      (fiberwiseFunctorRestrict F D i s) =
    fiberwiseFunctorRestrict F D (SSet.yonedaEquiv.symm (i.app n x)) s
  rw [← fiberwiseFunctorRestrict_comp, SSet.yonedaEquiv_symm_comp]

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
