module

public import SerrePositivity.InfinityCategories.F1.CoherentFamilyCurryCoherence
public import SerrePositivity.InfinityCategories.F1.CoherentStraighteningCounitNaturality

/-!
概要：図式の族の分類と余単位のパラメーター制限に関する自然性。
方針：積の底上の同じ比較を curry し端点の等式を明示する。
規約：族とパラメーターの小ささを追加しない。
使われ方：普遍図式の余単位を任意の族へ制限する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories

/-- 概要：制限した族の分類と元の族の分類の制限を結ぶ。
方針：積の底上の比較を curry し終点を curry の自然性で同定する。
規約：族の制限の一致を等式で入力する。
使われ方：普遍族と任意の族の比較を共通の式で扱う。 -/
def coherentStraighteningFamilyBaseChangeIso {B K L : SSet.{u + 1}}
    (F : B ⊗ L ⟶ SpaceInfinity.{u}) (G : B ⊗ K ⟶ SpaceInfinity.{u})
    (i : L ⟶ K) (h : (B ◁ i) ≫ G = F) :
    FunctorIso
      (curry (smallFiberLeftStraighteningDiagram (leftUnstraighteningProjection F)
        (leftUnstraighteningProjection_hasSmallSimplexFibers F)))
      (i ≫ curry (smallFiberLeftStraighteningDiagram (leftUnstraighteningProjection G)
        (leftUnstraighteningProjection_hasSmallSimplexFibers G))) :=
  coherentFamilyCurryIso (coherentStraighteningRestrictionDiagramIso F G (B ◁ i) h) ≪≫
    eqToIso (congrArg (fun d ↦ SSet.HomotopyCategory.mk (functorVertex d))
      (curry_natural_left i (smallFiberLeftStraighteningDiagram (leftUnstraighteningProjection G)
        (leftUnstraighteningProjection_hasSmallSimplexFibers G))))

/-- 概要：族の余単位は分類の制限比較と通常のパラメーター前合成に関して可換。
方針：底変換の余単位の自然性を curry し合成と端点の移送を整理する。
規約：全高次パラメーターを保つ関手同型の等式。
使われ方：普遍余単位と選択分類の余単位の一致。 -/
lemma coherentStraighteningFamilyCounit_baseChange_naturality {B K L : SSet.{u + 1}}
    (F : B ⊗ L ⟶ SpaceInfinity.{u}) (G : B ⊗ K ⟶ SpaceInfinity.{u})
    (i : L ⟶ K) (h : (B ◁ i) ≫ G = F) :
    coherentStraighteningFamilyBaseChangeIso F G i h ≪≫
      (coherentStraighteningFamilyCounit G).precomp i ≪≫
        eqToIso (congrArg (fun d ↦ SSet.HomotopyCategory.mk (functorVertex d))
          ((curry_natural_left i G).symm.trans (congrArg curry h))) =
      coherentStraighteningFamilyCounit F := by
  have he := congrArg (fun e ↦ coherentFamilyCurryIso e)
    (coherentStraighteningCounit_baseChange_naturality F G (B ◁ i) h)
  simp only [coherentFamilyCurryIso_trans, coherentFamilyCurryIso_precomp] at he
  have hq := coherentFamilyCurryIso_eqToIso (A := B) (B := L) h
  rw [hq] at he
  apply Iso.ext
  have hh := congrArg Iso.hom he
  simpa only [coherentStraighteningFamilyBaseChangeIso, coherentStraighteningFamilyCounit,
    coherentFamilyCurryIso_eqToIso, Iso.trans_hom, Iso.symm_hom, eqToIso.hom, eqToIso.inv,
    Category.assoc,
    eqToHom_trans, eqToHom_trans_assoc] using hh

end SerrePositivity.InfinityCategories
