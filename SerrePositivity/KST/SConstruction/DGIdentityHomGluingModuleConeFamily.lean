module
public import SerrePositivity.KST.SConstruction.DGIdentityHomGluingConeAxes
public import SerrePositivity.KST.SConstruction.DGHomGluingConeFunctor

/-!
概要：元始域上の恒等 Hom gluing cone の全加群族を同じ二軸で表示する。
方針：実 perfect cone の元 Hom 作用をそのまま含め、第三 cochain 零と二軸回収を使う。
規約：元の全鎖写像を保持する。
使われ方：元 gluing cone と全自然な module cone の入力全比較。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  {P : Type w} [DGCategory R P] (F G : DGFunctor R P C)
  (a : ∀ x, ForgetEnrichment.of (Complex R) (F.obj x) ⟶
    ForgetEnrichment.of (Complex R) (G.obj x))
  (h : ∀ x y, F.map x y ≫
      eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) (F.obj x)) (a y) =
      G.map x y ≫ eHomWhiskerRight (Complex R) (a x)
        (ForgetEnrichment.of (Complex R) (G.obj y)))
local notation "I" => DGFunctor.id C
local notation "H" => dgIdentityHomGluingFunctor R C F G a h

/-- 概要：元始域上の同じ実 perfect cone の全加群族。
方針：元 Hom を変更しない包含で同じ元 cone 関手を制限。
規約：元の対象・全鎖写像を保持。使われ方：実 cone 入力全比較の終域。 -/
def dgIdentityHomGluingModuleConeFamily : DGFunctor R P (RightModule R C) :=
  dgPerfectModuleUnderlying R C ((H).comp (dgHomGluingConeFunctor R C C C (I) (I)))

/-- 概要：元実 cone 族の全 Hom 作用は同じ二軸・零第三成分。
方針：元第三 cochain 零と二軸の Yoneda Hom 作用の回収を合成する。
規約：全整数次数を保持。使われ方：指定入力同型の全自然性。 -/
lemma dgIdentityHomGluingModuleConeFamily_map (x y : P) (n : ℤ)
    (z : (homObject R P x y).X n) :
    ((dgIdentityHomGluingModuleConeFamily R C F G a h).map x y).f n z =
      dgGluingModuleConeElement R C
        (dgHomGluingTargetModuleMap R C C C (I) (I) ((H).obj x))
        (dgHomGluingTargetModuleMap R C C C (I) (I) ((H).obj y))
        (((F.comp (dgYoneda R C)).map x y).f n z)
        (((G.comp (dgYoneda R C)).map x y).f n z) 0 (sub_add_cancel n 1) :=
  (dgIdentityHomGluingFunctor_coneHomMap_apply R C F G a h x y n z).trans
    (congrArg₂ (fun α β => dgGluingModuleConeElement R C
      (dgHomGluingTargetModuleMap R C C C (I) (I) ((H).obj x))
      (dgHomGluingTargetModuleMap R C C C (I) (I) ((H).obj y)) α β 0 (sub_add_cancel n 1))
      (congrArg (fun f => f.f n z) (dgIdentityHomGluingFunctor_coneLeftMap R C F G a h x y))
      (congrArg (fun f => f.f n z) (dgIdentityHomGluingFunctor_coneRightMap R C F G a h x y)))
end SerrePositivity.KST.SConstruction
