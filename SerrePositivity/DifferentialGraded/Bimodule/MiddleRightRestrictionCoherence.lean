module
public import SerrePositivity.DifferentialGraded.Bimodule.MiddleRestrictionMaps
public import SerrePositivity.DifferentialGraded.Bimodule.ValueIsomorphism
public import SerrePositivity.DifferentialGraded.Module.RestrictionCoherence

/-! # 右側の中間制限の恒等・合成自然同型 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z t
namespace SerrePositivity.DifferentialGraded.BimoduleCategory
open CategoryTheory Opposite CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (L : Type t) [DGCategory A L]

/-- 恒等右制限は、既存の右加群の恒等制限比較で元のbimoduleに戻る。 -/
def middleRightRestrictionIdObjIso (Q : BimoduleCategory A D L) :
    (middleRightRestrictionFunctor A D D L (DGFunctor.id D)).obj Q ≅ Q :=
  isoOfValueFamily A D L
    (M := (middleRightRestrictionFunctor A D D L (DGFunctor.id D)).obj Q) (N := Q)
    (fun l => moduleRestrictionIdObjIso A D ((evaluation A D L l).obj Q)) (by
      intro d l l'
      simp only [moduleRestrictionIdObjIso_hom_eval]
      apply hom_naturality_of_apply
      intro p f
      refine (Cochain.comp_id _).trans ?_
      refine Eq.trans ?_ (Cochain.id_comp _).symm
      exact congrArg (fun k => k.f p f)
        (Bimodule.rightRestriction_leftAt_map A D D L (DGFunctor.id D)
          (underlying A D L Q) d l l'))

@[simp]
lemma middleRightRestrictionIdObjIso_hom_value (Q : BimoduleCategory A D L) (d : D) (l : L) :
    (valueEvaluation A D L d l).map (middleRightRestrictionIdObjIso A D L Q).hom = 𝟙 _ :=
  moduleRestrictionIdObjIso_hom_eval A D ((evaluation A D L l).obj Q) d

def middleRightRestrictionIdIso :
    middleRightRestrictionFunctor A D D L (DGFunctor.id D) ≅ 𝟭 (BimoduleCategory A D L) :=
  NatIso.ofComponents (middleRightRestrictionIdObjIso A D L) (by
    intro Q Q' f
    apply hom_ext
    intro l
    exact (moduleRestrictionIdIso A D).hom.naturality (f.val l))

variable (E : Type w) [DGCategory A E] [Small.{u} E]
  (T : Type z) [DGCategory A T] [Small.{u} T]
  (F : DGFunctor A D E) (G : DGFunctor A E T)

/-- 二段階の右制限と合成dg関手の右制限を、既存の加群制限比較で結ぶ。 -/
def middleRightRestrictionCompObjIso (Q : BimoduleCategory A T L) :
    (middleRightRestrictionFunctor A E D L F).obj
        ((middleRightRestrictionFunctor A T E L G).obj Q) ≅
      (middleRightRestrictionFunctor A T D L (F.comp G)).obj Q :=
  isoOfValueFamily A D L
    (M := (middleRightRestrictionFunctor A E D L F).obj
      ((middleRightRestrictionFunctor A T E L G).obj Q))
    (N := (middleRightRestrictionFunctor A T D L (F.comp G)).obj Q)
    (fun l => moduleRestrictionCompObjIso A D E T F.op G.op ((evaluation A T L l).obj Q)) (by
      intro d l l'
      simp only [moduleRestrictionCompObjIso_hom_eval]
      apply hom_naturality_of_apply
      intro p f
      refine (Cochain.comp_id _).trans ?_
      refine Eq.trans ?_ (Cochain.id_comp _).symm
      have h₁ := Bimodule.rightRestriction_leftAt_map A E D L F
        (Bimodule.rightRestriction A T E L G (underlying A T L Q)) d l l'
      have h₂ := Bimodule.rightRestriction_leftAt_map A T E L G
        (underlying A T L Q) (F.obj d) l l'
      have h₃ := Bimodule.rightRestriction_leftAt_map A T D L (F.comp G)
        (underlying A T L Q) d l l'
      exact congrArg (fun k => k.f p f) (h₁.trans (h₂.trans h₃.symm)))

@[simp]
lemma middleRightRestrictionCompObjIso_hom_value (Q : BimoduleCategory A T L) (d : D) (l : L) :
    (valueEvaluation A D L d l).map
        (middleRightRestrictionCompObjIso A D L E T F G Q).hom = 𝟙 _ :=
  moduleRestrictionCompObjIso_hom_eval A D E T F.op G.op ((evaluation A T L l).obj Q) d

def middleRightRestrictionCompIso :
    middleRightRestrictionFunctor A T E L G ⋙ middleRightRestrictionFunctor A E D L F ≅
      middleRightRestrictionFunctor A T D L (F.comp G) :=
  NatIso.ofComponents (middleRightRestrictionCompObjIso A D L E T F G) (by
    intro Q Q' f
    apply hom_ext
    intro l
    exact (moduleRestrictionCompIso A D E T F.op G.op).hom.naturality (f.val l))

end SerrePositivity.DifferentialGraded.BimoduleCategory
