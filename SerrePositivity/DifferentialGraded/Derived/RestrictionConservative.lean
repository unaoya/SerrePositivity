module
public import SerrePositivity.DifferentialGraded.Derived.FunctorExtensionTriangles
public import SerrePositivity.DifferentialGraded.Derived.FunctorExtensionRepresentable
public import SerrePositivity.DifferentialGraded.Perfect.Compact.Enhancement

/-! # 本質的全射なdg関手に沿う導来制限の保守性

## 概要
本質的全射なdg関手に沿う導来制限の保守性。

## 方針
既存の制限表示と指定K-flatモデルの計算を局所化へ移し、実際の比較射の経路を照合する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。U16dで指定の制限squareを使う際の候補。一般Morita・tensor・
Hochschild型構成のモデル比較にも利用できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits Pretriangulated
variable (A : Type u) [CommRing A]

/-- dg Yonedaを主Kへ送り、右加群の主導来圏へ局所化する。 -/
def representableHomotopyToDerived (E : Type w) [DGCategory A E] [Small.{u} E] :
    HomotopyCategory A E ⥤ DerivedModuleCategory A E :=
  (dgYoneda A E).onHomotopy ⋙ moduleHomotopyToDerivedClosed A E

/-- 閉零対象でのYoneda像は実際の代表加群の主導来像。 -/
def representableHomotopyToDerivedComputation (E : Type w) [DGCategory A E] [Small.{u} E]
    (e : ClosedCategory A E) :
    (representableHomotopyToDerived A E).obj ((toHomotopy A E).obj e) ≅
      (moduleToDerived A E).obj
        (ForgetEnrichment.of (Complex A) (representable A (ForgetEnrichment.to (Complex A) e))) :=
  (moduleHomotopyToDerivedClosed A E).mapIso
    (eqToIso (congrArg (fun G => G.obj e) (dgYoneda A E).onHomotopy_fac)) ≪≫
      (moduleToHomotopyDerivedIso A E).app ((dgYoneda A E).onClosed.obj e)

variable (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D E)

lemma dgDerivedExtension_representable_essImage (hF : F.onHomotopy.EssSurj) (e : E) :
    ∃ d : D, Nonempty ((dgDerivedExtension A D E F).obj
      ((moduleToDerived A D).obj (ForgetEnrichment.of (Complex A) (representable A d))) ≅
        (moduleToDerived A E).obj (ForgetEnrichment.of (Complex A) (representable A e))) := by
  let := hF
  let Y := (toHomotopy A E).obj (ForgetEnrichment.of (Complex A) e)
  let X := F.onHomotopy.objPreimage Y
  let d := ForgetEnrichment.to (Complex A) X.as
  let i := F.onHomotopy.objObjPreimageIso Y
  let H := representableHomotopyToDerived A E
  have h₀ := representableHomotopyToDerivedComputation A E (F.onClosed.obj X.as)
  refine ⟨d, ⟨dgDerivedExtensionRepresentableIso A D E F d ≪≫ ?_⟩⟩
  exact h₀.symm ≪≫ H.mapIso i ≪≫
    representableHomotopyToDerivedComputation A E (ForgetEnrichment.of (Complex A) e)

local instance restrictionConservativeCommShift : (dgDerivedRestriction A D E F).CommShift ℤ :=
  dgDerivedRestrictionCommShift A D E F
local instance restrictionConservativeTriangulated :
    (dgDerivedRestriction A D E F).IsTriangulated :=
  dgDerivedRestrictionIsTriangulated A D E F

/-- 主K上の本質的全射性だけから導来制限は零対象を反映する。 -/
lemma dgDerivedRestriction_reflectsZero (hF : F.onHomotopy.EssSurj)
    (X : DerivedModuleCategory A E) (hX : IsZero ((dgDerivedRestriction A D E F).obj X)) :
    IsZero X := by
  apply (moduleRepresentables_detect_zero A E X).mpr
  intro e n
  obtain ⟨d, ⟨ei⟩⟩ := dgDerivedExtension_representable_essImage A D E F hF e
  let R := dgDerivedRestriction A D E F
  have hz : IsZero (R.obj (X⟦n⟧)) :=
    ((shiftFunctor (DerivedModuleCategory A D) n).map_isZero hX).of_iso
      ((R.commShiftIso n).app X)
  let G := (moduleToDerived A D).obj (ForgetEnrichment.of (Complex A) (representable A d))
  let eh := (Iso.homCongr ei.symm (Iso.refl (X⟦n⟧))).trans
    ((dgDerivedExtensionRestrictionAdjunction A D E F).homEquiv G (X⟦n⟧))
  exact ⟨fun f g => eh.injective (hz.eq_of_tgt (eh f) (eh g))⟩

lemma dgDerivedRestriction_reflectsIso (hF : F.onHomotopy.EssSurj)
    {X Y : DerivedModuleCategory A E} (f : X ⟶ Y)
    [IsIso ((dgDerivedRestriction A D E F).map f)] : IsIso f := by
  obtain ⟨Z, g, h, hT⟩ := distinguished_cocone_triangle f
  let T := Triangle.mk f g h
  let R := dgDerivedRestriction A D E F
  have hRT := R.map_distinguished T hT
  have hz : IsZero (R.obj Z) :=
    ((R.mapTriangle.obj T).isZero₃_iff_isIso₁ hRT).2 (by
      change IsIso ((dgDerivedRestriction A D E F).map f)
      infer_instance)
  exact (T.isZero₃_iff_isIso₁ hT).1 (dgDerivedRestriction_reflectsZero A D E F hF Z hz)

lemma dgDerivedRestrictionReflectsIsomorphisms (hF : F.onHomotopy.EssSurj) :
    (dgDerivedRestriction A D E F).ReflectsIsomorphisms where
  reflects f := dgDerivedRestriction_reflectsIso A D E F hF f

end SerrePositivity.DifferentialGraded
