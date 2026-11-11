module
public import SerrePositivity.KST.SConstruction.DGKUniverseLiftSmall
public import SerrePositivity.KST.SConstruction.DGFunctorClosedFamilyIso

/-! # 対象宇宙を上げても同じ閉同型族と全 Hom 自然性を保つ
概要：元の閉同型族を、同じ Hom を持つ対象宇宙の持ち上げへ運ぶ。
方針：順逆射・全 Hom の前後合成をそのまま使い、元の dg 関手 Hom end に束ねる。
規約：自然変換を対象ごとに選び直さない。使われ方：固定 S の比較辺の元の入力同型。
-/
@[expose] public section
noncomputable section
universe u v w r s
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (E : Type w) [DGCategory R E]

/-- 対象宇宙を上げた同じ二対象の間に、元の順逆射を保つ閉同型を置く。 -/
def dgUniverseLiftClosedIso (x y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift.{w, s} E)
    (e : ForgetEnrichment.of (Complex R) x.label.down ≅
      ForgetEnrichment.of (Complex R) y.label.down) :
    ForgetEnrichment.of (Complex R) x ≅ ForgetEnrichment.of (Complex R) y where
  hom := e.hom
  inv := e.inv
  hom_inv_id := e.hom_inv_id
  inv_hom_id := e.inv_hom_id

/-- 同じ順射による全 Hom 後合成は、元の後合成そのもの。 -/
lemma dgUniverseLiftClosedIso_whiskerLeft (x y z : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift.{w, s} E) (e) :
    eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) z)
      (dgUniverseLiftClosedIso R E x y e).hom =
    eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) z.label.down) e.hom := rfl

/-- 同じ順射による全 Hom 前合成も、元の前合成そのもの。 -/
lemma dgUniverseLiftClosedIso_whiskerRight (x y z : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift.{w, s} E) (e) :
    eHomWhiskerRight (Complex R) (dgUniverseLiftClosedIso R E x y e).hom
      (ForgetEnrichment.of (Complex R) z) =
    eHomWhiskerRight (Complex R) e.hom (ForgetEnrichment.of (Complex R) z.label.down) := rfl

variable (D : Type v) [DGCategory R D] [Small.{u} D] (F G : DGFunctor R D E)
  (e : ∀ x : D, ForgetEnrichment.of (Complex R) (F.obj x) ≅
    ForgetEnrichment.of (Complex R) (G.obj x))
  (h : ∀ x y : D, F.map x y ≫
    eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) (F.obj x)) (e y).hom =
    G.map x y ≫ eHomWhiskerRight (Complex R) (e x).hom
      (ForgetEnrichment.of (Complex R) (G.obj y)))

/-- 元の全 Hom 自然な同型族を、持ち上げ後も同じ全次数 Hom end の閉同型にする。 -/
def dgUniverseLiftFunctorClosedIso :
    ForgetEnrichment.of (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftFunctor.{u, v, w, r, s} F) ≅
    ForgetEnrichment.of (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftFunctor.{u, v, w, r, s} G) :=
  dgFunctorClosedIsoFromFamily R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift.{v, r} D) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift.{w, s} E)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftFunctor F) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftFunctor G)
    (fun x => dgUniverseLiftClosedIso R E _ _ (e x.label.down))
    (fun x y => h x.label.down y.label.down)

/-- 持ち上げ後の実 Hom end の順射の評価は、元の指定順射を保つ。 -/
lemma dgUniverseLiftFunctorClosedIso_hom_eval (x : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift.{v, r} D) :
    (dgFunctorEvaluationDG R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift.{v, r} D) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift.{w, s} E) x).onClosed.map
      (dgUniverseLiftFunctorClosedIso R E D F G e h).hom =
    (dgUniverseLiftClosedIso R E _ _ (e x.label.down)).hom :=
  dgFunctorClosedHomFromFamily_eval R _ _ _ _ _ _ x

/-- 同じ Hom end の逆射の評価も、元の指定逆射を保つ。 -/
lemma dgUniverseLiftFunctorClosedIso_inv_eval (x : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift.{v, r} D) :
    (dgFunctorEvaluationDG R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift.{v, r} D) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift.{w, s} E) x).onClosed.map
      (dgUniverseLiftFunctorClosedIso R E D F G e h).inv =
    (dgUniverseLiftClosedIso R E _ _ (e x.label.down)).inv :=
  dgFunctorClosedHomFromFamily_eval R _ _ _ _ _ _ x

end SerrePositivity.KST.SConstruction
