module
public import SerrePositivity.KST.SConstruction.DGHomGluingTargetCone
public import SerrePositivity.DifferentialGraded.Perfect.RepresentableHomology
public import SerrePositivity.DifferentialGraded.Module.ConeRotation

/-! # 同型である元の Hom gluing 比較の cone の収縮
概要：元の比較が閉零同型なら、その同じ実 cone は加群ホモトピー圏で零。
方針：元の Yoneda 同型で cone を恒等 cone へ移し、D の指定収縮を使う。
規約：対象別の結論。入力関手間の自然な収縮を主張しない。
使われ方：実対角像を消す商からの比較の対象別入力。
-/
@[expose] public section
noncomputable section
universe u v w z
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (E : Type z) [DGCategory R E] [Small.{u} E]
  (p : DGFunctor R C E) (q : DGFunctor R D E)
variable (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D (dgHomGluingBimodule R C D E p q))

/-- 元の加群同型の cone を、その終域の恒等 cone と同定する。 -/
def dgHomGluingModuleConeIsoIdentity {U V : ModuleCategory R E} (e : U ≅ V) :
    moduleCone R E e.hom ≅ moduleCone R E (𝟙 V) :=
  moduleConeIsoOfArrowIso R E e.hom (𝟙 V)
    (Arrow.isoMk' e.hom (𝟙 V) e (Iso.refl V) (by simp))

/-- 同じ実 cone を、元の比較同型を使う同じ恒等 cone へ送る指定同型。 -/
def dgHomGluingTargetConeIsoIdentity
  (e : ForgetEnrichment.of (Complex R) (p.obj X.left) ≅
    ForgetEnrichment.of (Complex R) (q.obj X.right))
  (he : dgHomGluingTargetMap R C D E p q X = e.hom) :
    moduleCone R E (dgHomGluingTargetModuleMap R C D E p q X) ≅
      moduleCone R E (𝟙 (ForgetEnrichment.of (Complex R) (representable R (q.obj X.right)))) := by
  let Y := (dgYoneda R E).onClosed
  let ey := Y.mapIso e
  have hm : dgHomGluingTargetModuleMap R C D E p q X = ey.hom := congrArg Y.map he
  exact eqToIso (congrArg (moduleCone R E) hm) ≪≫ dgHomGluingModuleConeIsoIdentity R E ey

/-- 同じ元の比較の実 cone は、加群ホモトピー圏で零対象。 -/
lemma dgHomGluingTargetCone_isZero
  (e : ForgetEnrichment.of (Complex R) (p.obj X.left) ≅
    ForgetEnrichment.of (Complex R) (q.obj X.right))
  (he : dgHomGluingTargetMap R C D E p q X = e.hom) :
    IsZero ((moduleToHomotopy R E).obj
      (moduleCone R E (dgHomGluingTargetModuleMap R C D E p q X))) :=
  (moduleConeId_isZero R E
    (ForgetEnrichment.of (Complex R) (representable R (q.obj X.right)))).of_iso
      (((moduleToHomotopy R E).mapIso
        (dgHomGluingTargetConeIsoIdentity R C D E p q X e he)))

end SerrePositivity.KST.SConstruction
