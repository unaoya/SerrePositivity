module

public import SerrePositivity.KST.DerivedGeometry.FreeSheafOnOpen
public import Mathlib.CategoryTheory.Adjunction.Additive

/-!
概要：自由表現可能加群前層からの Hom と切断の加法的な比較。
方針：自由加群の随伴と Yoneda の同値を合成し、標準生成元上で加法性を示す。
規約：係数環の可換性は不要。
使われ方：TT §3・§8、Toën §3.2 の自由 Čech 鎖複体への Hom の比較。
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
概要：自由表現可能加群前層からの射は同じ開の切断と対応する。
方針：自由加群の随伴を前層へ拡張し Yoneda の同値を合成する。
規約：元の自由加群前層の Hom を使う。
使われ方：TT §3、Toën §3.2 の Čech の各項の Hom 比較。
-/
def freeModulePresheafOnOpenHomEquiv (U : Opens X)
    (P : (Opens X)ᵒᵖ ⥤ ModuleCat.{u} R) :
    ((freeModulePresheafOnOpen R X).obj U ⟶ P) ≃ P.obj (.op U) :=
  (((ModuleCat.adj R).whiskerRight ((Opens X)ᵒᵖ)).homEquiv _ P).trans yonedaEquiv

/--
概要：Hom と切断の対応は恒等射に対応する自由生成元での評価。
方針：自由加群の随伴と Yoneda の定義を展開する。
規約：この評価式から加法性を導く。
使われ方：TT §3、Toën §3.2 の加法的な Čech 比較。
-/
lemma freeModulePresheafOnOpenHomEquiv_apply (U : Opens X)
    (P : (Opens X)ᵒᵖ ⥤ ModuleCat.{u} R)
    (f : (freeModulePresheafOnOpen R X).obj U ⟶ P) :
    freeModulePresheafOnOpenHomEquiv R X U P f =
      f.app (.op U) (ModuleCat.freeMk (𝟙 U)) := by
  rfl

/--
概要：自由表現可能加群前層からの Hom と切断の対応は加法的同値。
方針：標準生成元での評価式を使い加法性を証明する。
規約：非可換係数でも加法群として比較する。
使われ方：TT §3・§8、Toën §3.2 の Hom 複体の微分比較。
-/
def freeModulePresheafOnOpenHomAddEquiv (U : Opens X)
    (P : (Opens X)ᵒᵖ ⥤ ModuleCat.{u} R) :
    ((freeModulePresheafOnOpen R X).obj U ⟶ P) ≃+ P.obj (.op U) where
  toEquiv := freeModulePresheafOnOpenHomEquiv R X U P
  map_add' f g := by rfl

/--
概要：自由前層の Hom と切断の同値は開の包含と可換。
方針：自由加群の随伴の左自然性と Yoneda の自然性を合成する。
規約：切断側は実際の制限写像。
使われ方：TT §3・§8、Toën §3.2 の自由 Čech の Hom 比較の自然性。
-/
lemma freeModulePresheafOnOpenHomEquiv_naturality {V U : Opens X} (f : V ⟶ U)
    (P : (Opens X)ᵒᵖ ⥤ ModuleCat.{u} R)
    (g : (freeModulePresheafOnOpen R X).obj U ⟶ P) :
    freeModulePresheafOnOpenHomEquiv R X V P ((freeModulePresheafOnOpen R X).map f ≫ g) =
      P.map f.op (freeModulePresheafOnOpenHomEquiv R X U P g) := by
  let B := (ModuleCat.adj R).whiskerRight ((Opens X)ᵒᵖ)
  have h := B.homEquiv_naturality_left (yoneda.map f) g
  exact (congrArg yonedaEquiv h).trans (yonedaEquiv_naturality _ f).symm

end SerrePositivity.KST.DerivedGeometry
