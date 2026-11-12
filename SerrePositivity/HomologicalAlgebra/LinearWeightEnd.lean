module
public import SerrePositivity.HomologicalAlgebra.FunctorComplexExchange
public import SerrePositivity.HomologicalAlgebra.FreePresheafLinearHom
public import SerrePositivity.DifferentialGraded.Complexes.HomComplex
public import Mathlib.CategoryTheory.Linear.Yoneda

/-!
概要：加群値の線形重みから非有界複体値図式への end の複体。
方針：図式圏の線形 Hom を各複体次数で取り、微分は元の図式の微分との後合成とする。
規約：次数 q の元は重みから X の次数 q の図式への自然変換。積だけで自然性条件を省略しない。
使われ方：HA 1.2.4、G10 の標準単体重みと BK 重みの比較。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits Opposite
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.HomologicalAlgebra
variable (A : Type u) [CommRing A] {J : Type} [SmallCategory J]

/-- 線形 end の対象複体。次数 q の元は W から X の次数 q への自然変換。 -/
def linearWeightEndComplex (W : Jᵒᵖ ⥤ ModuleCat.{u} A) (X : Jᵒᵖ ⥤ Complex A) : Complex A :=
  (((linearCoyoneda A (Jᵒᵖ ⥤ ModuleCat.{u} A)).obj (op W)).mapHomologicalComplex
    (.up ℤ)).obj ((functorToComplexOfFunctors Jᵒᵖ (ModuleCat.{u} A) (.up ℤ)).obj X)

/-- 係数の射による、同じ線形 end の後合成。 -/
def linearWeightEndCoefficientMap (W : Jᵒᵖ ⥤ ModuleCat.{u} A)
    {X Y : Jᵒᵖ ⥤ Complex A} (f : X ⟶ Y) :
    linearWeightEndComplex A W X ⟶ linearWeightEndComplex A W Y where
  f q := ((linearCoyoneda A (Jᵒᵖ ⥤ ModuleCat.{u} A)).obj (op W)).map
    (((functorToComplexOfFunctors Jᵒᵖ (ModuleCat.{u} A) (.up ℤ)).map f).f q)
  comm' q r hqr := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    apply NatTrans.ext
    funext j
    exact congrArg (fun k => z.app j ≫ k) ((f.app j).comm q r)

/-- 重みの射による、同じ線形 end の前合成。 -/
def linearWeightEndWeightMap (X : Jᵒᵖ ⥤ Complex A)
    {V W : Jᵒᵖ ⥤ ModuleCat.{u} A} (g : V ⟶ W) :
    linearWeightEndComplex A W X ⟶ linearWeightEndComplex A V X where
  f q := ((linearCoyoneda A (Jᵒᵖ ⥤ ModuleCat.{u} A)).map g.op).app
    (X ⋙ HomologicalComplex.eval (ModuleCat.{u} A) (.up ℤ) q)
  comm' q r hqr := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    apply NatTrans.ext
    funext j
    exact Category.assoc _ _ _

/-- 固定した加群重みからの線形 end を、複体値図式の全関手として取る。 -/
def linearWeightEndFunctor (W : Jᵒᵖ ⥤ ModuleCat.{u} A) :
    (Jᵒᵖ ⥤ Complex A) ⥤ Complex A where
  obj X := linearWeightEndComplex A W X
  map f := linearWeightEndCoefficientMap A W f
  map_id X := by
    apply HomologicalComplex.Hom.ext
    funext q
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    apply NatTrans.ext
    funext j
    exact Category.comp_id _
  map_comp f g := by
    apply HomologicalComplex.Hom.ext
    funext q
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    apply NatTrans.ext
    funext j
    exact (Category.assoc _ _ _).symm

/-- 同じ線形 end は重みの射に反変に自然。 -/
def linearWeightEnd (X : Jᵒᵖ ⥤ Complex A) :
    (Jᵒᵖ ⥤ ModuleCat.{u} A)ᵒᵖ ⥤ Complex A where
  obj W := linearWeightEndComplex A W.unop X
  map f := linearWeightEndWeightMap A X f.unop
  map_id W := by
    apply HomologicalComplex.Hom.ext
    funext q
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    apply NatTrans.ext
    funext j
    exact Category.id_comp _
  map_comp f g := by
    apply HomologicalComplex.Hom.ext
    funext q
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    apply NatTrans.ext
    funext j
    exact Category.assoc _ _ _

/-- 線形 end の同じ重みの射は、係数図式の射と可換。 -/
theorem linearWeightEnd_naturality {X Y : Jᵒᵖ ⥤ Complex A} (f : X ⟶ Y)
    {W V : Jᵒᵖ ⥤ ModuleCat.{u} A} (g : V ⟶ W) :
    (linearWeightEnd A X).map g.op ≫ (linearWeightEndFunctor A V).map f =
      (linearWeightEndFunctor A W).map f ≫ (linearWeightEnd A Y).map g.op := by
  apply HomologicalComplex.Hom.ext
  funext q
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  apply NatTrans.ext
  funext j
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

/-- 自由重みからの線形 end は、元の指定対象での線形 Hom 複体。 -/
def freeWeightEndIso (P : ModuleCat.{u} A) (j : J) (X : Jᵒᵖ ⥤ Complex A) :
    (linearWeightEndFunctor A ((freePresheafFunctor J P).obj j)).obj X ≅
      (((linearCoyoneda A (ModuleCat.{u} A)).obj (op P)).mapHomologicalComplex (.up ℤ)).obj
        (X.obj (op j)) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun q => (freePresheafHomLinearEquiv (R := A) P j
      (X ⋙ HomologicalComplex.eval (ModuleCat.{u} A) (.up ℤ) q)).toModuleIso)
    (fun q r hqr => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro z
      exact freePresheafHomLinearEquiv_comp P j z
        (((functorToComplexOfFunctors Jᵒᵖ (ModuleCat.{u} A) (.up ℤ)).obj X).d q r) |>.symm)

/-- 重みの鎖ホモトピーを移すための、同じ end 関手の加法性。 -/
instance linearWeightEnd_additive (X : Jᵒᵖ ⥤ Complex A) : (linearWeightEnd A X).Additive where
  map_add {W V} f g := by
    apply HomologicalComplex.Hom.ext
    funext q
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    apply NatTrans.ext
    funext j
    change (f.unop.app j + g.unop.app j) ≫ z.app j =
      f.unop.app j ≫ z.app j + g.unop.app j ≫ z.app j
    rw [CategoryTheory.Preadditive.add_comp]

/-- 自由重みの評価同型は元の複体値図式の全射に自然。 -/
def freeWeightEndNatIso (P : ModuleCat.{u} A) (j : J) :
    linearWeightEndFunctor A ((freePresheafFunctor J P).obj j) ≅
      (evaluation Jᵒᵖ (Complex A)).obj (op j) ⋙
        ((linearCoyoneda A (ModuleCat.{u} A)).obj (op P)).mapHomologicalComplex (.up ℤ) :=
  NatIso.ofComponents (freeWeightEndIso A P j) (by
    intro X Y f
    apply HomologicalComplex.Hom.ext
    funext q
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    rfl)

/-- 係数図式と反変な重みを共に動かす、同じ線形 end の全関手族。 -/
def linearWeightEndFamily :
    (Jᵒᵖ ⥤ Complex A) ⥤ (Jᵒᵖ ⥤ ModuleCat.{u} A)ᵒᵖ ⥤ Complex A where
  obj X := linearWeightEnd A X
  map f :=
    { app W := linearWeightEndCoefficientMap A W.unop f
      naturality W V g := by
        apply HomologicalComplex.Hom.ext
        funext q
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro z
        apply NatTrans.ext
        funext j
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        rfl }
  map_id X := by
    apply NatTrans.ext
    funext W
    apply HomologicalComplex.Hom.ext
    funext q
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    apply NatTrans.ext
    funext j
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl
  map_comp f g := by
    apply NatTrans.ext
    funext W
    apply HomologicalComplex.Hom.ext
    funext q
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    apply NatTrans.ext
    funext j
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl

end SerrePositivity.HomologicalAlgebra
