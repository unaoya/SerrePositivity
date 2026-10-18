module

public import SerrePositivity.KST.DerivedGeometry.FreePresheafHom
public import SerrePositivity.KST.DerivedGeometry.CoproductHomAddEquiv
public import SerrePositivity.KST.DerivedGeometry.AdditiveProductIso
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import Mathlib.CategoryTheory.Limits.FormalCoproducts.Basic

/-!
概要：形式的余積の自由層からの Hom と各開の切断の積の比較。
方針：層化の加法的随伴、余積の Hom、自由表現可能前層の加法的 Yoneda を合成する。
規約：非可換係数でも加法群として比較する。
使われ方：TT §3・§8、BvdB Thm 3.1.1、Toën §3.2 の injective Čech 計算。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits TopologicalSpace
namespace SerrePositivity.KST.DerivedGeometry
variable (R : Type u) [Ring R] (X : TopCat.{u})

/--
概要：形式的余積を自由前層で評価して層化する関手。
方針：各開の自由前層の余積に実際の層化を適用する。
規約：自由 Čech 鎖複体と同じ対象を用いる。
使われ方：TT §3・§8、Toën §3.2 の自由 Čech の Hom 比較。
-/
def freeFormalSheafFunctor : FormalCoproduct.{u} (Opens X) ⥤
    Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R) :=
  (FormalCoproduct.eval (Opens X) ((Opens X)ᵒᵖ ⥤ ModuleCat.{u} R)).obj
    (freeModulePresheafOnOpen R X) ⋙ presheafToSheaf _ _

/--
概要：形式的余積の自由層からの射は開ごとの切断の族と加法的に同値。
方針：層化の随伴と余積の Hom の同値と自由前層の Yoneda の同値を合成する。
規約：Hom と切断の両方に実際の加法群構造を使う。
使われ方：TT §3・§8、Toën §3.2 の Hom 余鎖複体。
-/
def freeFormalSheafHomAddEquiv (Z : FormalCoproduct.{u} (Opens X))
    (I : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)) :
    ((freeFormalSheafFunctor R X).obj Z ⟶ I) ≃+ (∀ i : Z.I, I.obj.obj (.op (Z.obj i))) :=
  ((sheafificationAdjunction _ _).homAddEquiv _ I).trans
    ((coproductHomAddEquiv
      (fun i : Z.I => (freeModulePresheafOnOpen R X).obj (Z.obj i)) I.obj).trans
        (AddEquiv.piCongrRight (fun i => freeModulePresheafOnOpenHomAddEquiv R X (Z.obj i) I.obj)))

/--
概要：自由層の Hom 比較の各成分は余積の挿入射への制限で計算できる。
方針：構成した三つの加法的同値の定義を展開する。
規約：後続の自然性の証明に使う評価式。
使われ方：TT §3、Toën §3.2 の Čech 微分の Hom 比較。
-/
lemma freeFormalSheafHomAddEquiv_apply (Z : FormalCoproduct.{u} (Opens X))
    (I : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R))
    (g : (freeFormalSheafFunctor R X).obj Z ⟶ I) (i : Z.I) :
    freeFormalSheafHomAddEquiv R X Z I g i =
      freeModulePresheafOnOpenHomEquiv R X (Z.obj i) I.obj
        (Sigma.ι (fun i : Z.I => (freeModulePresheafOnOpen R X).obj (Z.obj i)) i ≫
          (sheafificationAdjunction _ _).homEquiv _ I g) := rfl

/--
概要：形式的余積の自由層の Hom 比較は各包含・添字写像について自然。
方針：層化の随伴の自然性と余積の挿入公式を経て自由前層の Yoneda の自然性を使う。
規約：形式的余積の全ての射を扱う。
使われ方：TT §3・§8、Toën §3.2 の Čech 微分の Hom 比較。
-/
lemma freeFormalSheafHomAddEquiv_naturality
    {Z Z' : FormalCoproduct.{u} (Opens X)} (f : Z ⟶ Z')
    (I : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R))
    (g : (freeFormalSheafFunctor R X).obj Z' ⟶ I) (i : Z.I) :
    freeFormalSheafHomAddEquiv R X Z I ((freeFormalSheafFunctor R X).map f ≫ g) i =
      I.obj.map (f.φ i).op (freeFormalSheafHomAddEquiv R X Z' I g (f.f i)) := by
  let F := freeModulePresheafOnOpen R X
  let B := sheafificationAdjunction (Opens.grothendieckTopology X) (ModuleCat.{u} R)
  let E := (FormalCoproduct.eval (Opens X) ((Opens X)ᵒᵖ ⥤ ModuleCat.{u} R)).obj F
  let g' : E.obj Z' ⟶ I.obj := B.homEquiv _ I g
  have h₁ := B.homEquiv_naturality_left (E.map f) g
  have h₂ : Sigma.ι (fun i : Z.I => F.obj (Z.obj i)) i ≫ E.map f ≫ g' =
      F.map (f.φ i) ≫ Sigma.ι (F.obj ∘ Z'.obj) (f.f i) ≫ g' := by
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (fun k => k ≫ g')
      (Sigma.ι_comp_desc (fun j : Z.I => F.map (f.φ j) ≫
        Sigma.ι (F.obj ∘ Z'.obj) (f.f j)) i)).trans ?_
    exact Category.assoc _ _ _
  exact (congrArg (fun k => freeModulePresheafOnOpenHomEquiv R X (Z.obj i) I.obj
      (Sigma.ι (fun i : Z.I => F.obj (Z.obj i)) i ≫ k)) h₁).trans
    ((congrArg (freeModulePresheafOnOpenHomEquiv R X (Z.obj i) I.obj) h₂).trans
      (freeModulePresheafOnOpenHomEquiv_naturality R X (f.φ i) I.obj
        (Sigma.ι (F.obj ∘ Z'.obj) (f.f i) ≫ g')))

end SerrePositivity.KST.DerivedGeometry
