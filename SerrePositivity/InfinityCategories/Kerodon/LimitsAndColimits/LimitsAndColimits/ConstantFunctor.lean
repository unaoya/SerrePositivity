module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.ConstantAdjunct

/-!
概要：頂点とその間の射を定値関手と二胞体へ送る作用。
方針：第二射影の curry を使い、前後合成との整合を示す。
規約：定値関手の対象の表示の同一視を明示する。
使われ方：Kerodon Prop 6.2.1.17（Tag 02F1） の対象変数に関する自然性。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

/-- 概要：各頂点をその定値関手へ送る単体集合の射。
方針：第二射影を curry する。
規約：A,X に quasicategory 性は不要。
使われ方：対象の間の射をパラメータ A 上の二胞体へ移す。 -/
def constantFunctorMap (A X : SSet.{u}) : X ⟶ (ihom A).obj X :=
  curry (snd A X)

/-- 概要：定値関手の射の零単体での値は既存の関手頂点。
方針：内部 Hom の各成分で零単体からの唯一の射を同定する。
規約：任意の頂点 x。
使われ方：h Fun の対象の輸送。 -/
lemma constantFunctorMap_vertex (A : SSet.{u}) {X : SSet.{u}} (x : X _⦋0⦌) :
    (constantFunctorMap A X).app (Opposite.op ⦋0⦌) x =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.const x : A ⟶ X) := by
  apply CategoryTheory.Functor.functorHom_ext
  intro d α
  have hα : α = (SimplexCategory.const d.unop ⦋0⦌ 0).op := Subsingleton.elim _ _
  subst α
  apply ConcreteCategory.hom_ext
  intro a
  rfl

/-- 概要：定値関手への射はパラメータの前合成と整合する。
方針：uncurry すると第二射影を前合成する等式になる。
規約：i は任意の単体集合の射。
使われ方：定値二胞体のパラメータ自然性。 -/
lemma constantFunctorMap_precomp {A B X : SSet.{u}} (i : A ⟶ B) :
    constantFunctorMap B X ≫ (pre i).app X = constantFunctorMap A X := by
  apply uncurry_injective
  rw [uncurry_pre_app]
  simp only [constantFunctorMap, uncurry_curry]
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro z
  rfl

/-- 概要：定値関手への射は標的の射による後合成と整合する。
方針：uncurry の自然性と第二射影を計算する。
規約：F は任意の単体集合の射。
使われ方：対象変数の射の像と右 whisker の比較。 -/
lemma constantFunctorMap_postcomp (A : SSet.{u}) {X Y : SSet.{u}} (F : X ⟶ Y) :
    constantFunctorMap A X ≫ (ihom A).map F = F ≫ constantFunctorMap A Y := by
  apply uncurry_injective
  rw [uncurry_natural_right, uncurry_natural_left]
  simp only [constantFunctorMap, uncurry_curry]
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro z
  rfl

/-- 概要：ホモトピー圏の射を定値関手間の h Fun の二胞体へ送る。
方針：定値関手への射を h に写し、両端を既存の頂点表示へ揃える。
規約：X の quasicategory 性を仮定しない。
使われ方：写像空間への前後合成作用の指定。 -/
def constantFunctorHomMap (A : SSet.{u}) {X : SSet.{u}} {x y : X _⦋0⦌}
    (f : (SSet.HomotopyCategory.mk x : hoFunctor.obj X) ⟶ SSet.HomotopyCategory.mk y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.ConstantFunctorHom A X x y :=
  eqToHom (congrArg SSet.HomotopyCategory.mk (constantFunctorMap_vertex A x)).symm ≫
    (hoFunctor.map (constantFunctorMap A X)).toFunctor.map f ≫
      eqToHom (congrArg SSet.HomotopyCategory.mk (constantFunctorMap_vertex A y))

/-- 概要：定値二胞体への作用は恒等射を保つ。
方針：h の関手性と端点の輸送を相殺する。
規約：任意の単体集合 X とパラメータ A。
使われ方：写像空間の対象変数の恒等作用。 -/
lemma constantFunctorHomMap_id (A : SSet.{u}) {X : SSet.{u}} (x : X _⦋0⦌) :
    constantFunctorHomMap A (𝟙 (SSet.HomotopyCategory.mk x)) = 𝟙 _ := by
  simp [constantFunctorHomMap]

/-- 概要：定値二胞体への作用は射の合成を保つ。
方針：h の関手性と中間の端点の輸送を相殺する。
規約：任意の三頂点の間のホモトピー圏の射。
使われ方：対象変数の合成作用。 -/
lemma constantFunctorHomMap_comp (A : SSet.{u}) {X : SSet.{u}} {x y z : X _⦋0⦌}
    (f : (SSet.HomotopyCategory.mk x : hoFunctor.obj X) ⟶ SSet.HomotopyCategory.mk y)
    (g : (SSet.HomotopyCategory.mk y : hoFunctor.obj X) ⟶ SSet.HomotopyCategory.mk z) :
    constantFunctorHomMap A (f ≫ g) =
      constantFunctorHomMap A f ≫ constantFunctorHomMap A g := by
  simp [constantFunctorHomMap, Category.assoc]

/-- 概要：定値二胞体はパラメータの前合成と整合する。
方針：定値関手の単体的自然性を h に移し、射の輸送を照合する。
規約：パラメータに quasicategory 性は不要。
使われ方：写像空間の前後合成作用の族による特徴づけ。 -/
lemma constantFunctorHomMap_precomp {A B X : SSet.{u}} (i : A ⟶ B)
    {x y : X _⦋0⦌}
    (f : (SSet.HomotopyCategory.mk x : hoFunctor.obj X) ⟶ SSet.HomotopyCategory.mk y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHomPrecomp i (constantFunctorHomMap B f) =
      constantFunctorHomMap A f := by
  have h := congrArg (fun k : X ⟶ (ihom A).obj X ↦ (hoFunctor.map k).toFunctor)
    (constantFunctorMap_precomp (X := X) i)
  simp only [Functor.map_comp] at h
  have hh := CategoryTheory.Functor.congr_hom h f
  change (hoFunctor.map ((pre i).app X)).toFunctor.map
      ((hoFunctor.map (constantFunctorMap B X)).toFunctor.map f) = _ at hh
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHomPrecomp, constantFunctorHomMap, Functor.map_comp, eqToHom_map]
  rw [hh]
  simp

/-- 概要：定値二胞体の後合成は標的のホモトピー圏の射の像と一致する。
方針：単体的な後合成自然性を h に写し、定値関手の端点の同一視を補う。
規約：比較には constantFunctorCompIso の同じ輸送を使う。
使われ方：adjunct の対象変数の自然性のための右 whisker の計算。 -/
lemma constantFunctorHomMap_postcomp (A : SSet.{u}) {X Y : SSet.{u}} (F : X ⟶ Y)
    {x y : X _⦋0⦌}
    (f : (SSet.HomotopyCategory.mk x : hoFunctor.obj X) ⟶ SSet.HomotopyCategory.mk y) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.constantFunctorCompIso A x F).inv ≫
      (hoFunctor.map ((ihom A).map F)).toFunctor.map (constantFunctorHomMap A f) ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.constantFunctorCompIso A y F).hom =
      constantFunctorHomMap A ((hoFunctor.map F).toFunctor.map f) := by
  have h := congrArg (fun k : X ⟶ (ihom A).obj Y ↦ (hoFunctor.map k).toFunctor)
    (constantFunctorMap_postcomp A F)
  simp only [Functor.map_comp] at h
  have hh := CategoryTheory.Functor.congr_hom h f
  change (hoFunctor.map ((ihom A).map F)).toFunctor.map
      ((hoFunctor.map (constantFunctorMap A X)).toFunctor.map f) = _ at hh
  simp only [constantFunctorHomMap, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.constantFunctorCompIso, eqToIso.inv, eqToIso.hom,
    Functor.map_comp, eqToHom_map]
  rw [hh]
  simp

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
