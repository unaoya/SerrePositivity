module

public import SerrePositivity.DifferentialGraded.Module.Hom.HomotopyAndOperations
public import SerrePositivity.DifferentialGraded.Functor.DGFunctorHomWhiskering

/-!
# 既存の共変 Hom による加群 cotensor の全作用

概要：M10 の実 Hom 比較へ、同じ Hom(K,M) を取る加群と全射作用を渡す。
方針：homCovariantDG と元の加群 dg 関手を合成し、閉零射は既存の Hom 後合成で送る。
規約：HA §4.2.1、作用を複製せず、半自由性・モデル構造を仮定しない。
使われ方：同じ標準単体を使う right frame の候補と元の dg Hom の比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.EInfinity.Modules
open CategoryTheory MonoidalCategory Opposite
open SerrePositivity.DifferentialGraded
open SerrePositivity.KST.SConstruction
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]

/-- 概要：元の全 dg 加群の同じ共変 Hom との合成。
方針：既存の homCovariantDG を後合成する。
規約：HA §4.2.1、全斉次作用。使われ方：加群 cotensor の元の対象。 -/
def dgModuleCotensor (K : Complex A) (M : RightModule A D) : RightModule A D :=
  M.toFunctor.comp (homCovariantDG A K)

variable [Small.{u} D]

/-- 概要：同じ Hom(K,M) の閉零加群対象。
方針：同じ合成の閉零表示を使う。
規約：HA §4.2.1、元の主加群圏。使われ方：実モデルの frame の入力。 -/
abbrev moduleCotensor (K : Complex A) (M : ModuleCategory A D) : ModuleCategory A D :=
  ForgetEnrichment.of (Complex A) (dgModuleCotensor A D K (ForgetEnrichment.to (Complex A) M))

/-- 概要：同じ cotensor の台は点ごとの内部 Hom。
方針：元の合成を評価する。
規約：HA §4.2.1、同じ複体。使われ方：Reedy 判定の台の照合。 -/
lemma moduleCotensor_eval (K : Complex A) (M : ModuleCategory A D) (x : D) :
    (moduleEvaluation A D x).obj (moduleCotensor A D K M) =
      homComplex A K ((moduleEvaluation A D x).obj M) := rfl

/-- 概要：同じ閉零射の Hom 後合成は全 dg 作用と自然。
方針：既存の enriched 前後合成の交換と元の加群射の自然性を貼る。
規約：HA §4.2.1、全次数。使われ方：同じ cotensor の射作用。 -/
lemma moduleCotensorMap_naturality (K : Complex A) {M N : ModuleCategory A D}
    (f : M ⟶ N) (x y : Dᵒᵖ) :
    (dgModuleCotensor A D K (ForgetEnrichment.to (Complex A) M)).map x y ≫
      homPostcompose _ (homPostcompose K ((moduleEvaluation A D y.unop).map f)) =
    (dgModuleCotensor A D K (ForgetEnrichment.to (Complex A) N)).map x y ≫
      homPrecompose (homPostcompose K ((moduleEvaluation A D x.unop).map f)) _ := by
  let F := homCovariantDG A K
  let a := (moduleEvaluation A D x.unop).map f
  let b := (moduleEvaluation A D y.unop).map f
  have hp := enrichedFunctorHom_postcompose (Complex A) F b (homPostcompose K b)
    (homCovariantDG_closedMap A K b) ((ForgetEnrichment.to (Complex A) M).obj x)
  have hq := enrichedFunctorHom_precompose (Complex A) F a (homPostcompose K a)
    (homCovariantDG_closedMap A K a) ((ForgetEnrichment.to (Complex A) N).obj y)
  simp only [complexHomWhiskerLeft, complexHomWhiskerRight] at hp hq
  change homPostcompose ((ForgetEnrichment.to (Complex A) M).obj x) b ≫
      F.map ((ForgetEnrichment.to (Complex A) M).obj x) ((ForgetEnrichment.to (Complex A) N).obj y) =
    F.map ((ForgetEnrichment.to (Complex A) M).obj x) ((ForgetEnrichment.to (Complex A) M).obj y) ≫
      homPostcompose (F.obj ((ForgetEnrichment.to (Complex A) M).obj x)) (homPostcompose K b) at hp
  change homPrecompose a ((ForgetEnrichment.to (Complex A) N).obj y) ≫
      F.map ((ForgetEnrichment.to (Complex A) M).obj x) ((ForgetEnrichment.to (Complex A) N).obj y) =
    F.map ((ForgetEnrichment.to (Complex A) N).obj x) ((ForgetEnrichment.to (Complex A) N).obj y) ≫
      homPrecompose (homPostcompose K a) (F.obj ((ForgetEnrichment.to (Complex A) N).obj y)) at hq
  have h := (moduleMapFamilyEquiv A D M N f).property x y
  change (ForgetEnrichment.to (Complex A) M).map x y ≫ homPostcompose _ b =
    (ForgetEnrichment.to (Complex A) N).map x y ≫ homPrecompose a _ at h
  change ((ForgetEnrichment.to (Complex A) M).map x y ≫ F.map _ _) ≫
    homPostcompose _ (homPostcompose K b) =
    ((ForgetEnrichment.to (Complex A) N).map x y ≫ F.map _ _) ≫
      homPrecompose (homPostcompose K a) _
  rw [Category.assoc, ← hp, ← Category.assoc, h, Category.assoc, hq, ← Category.assoc]

/-- 概要：同じ cotensor の閉零射作用。
方針：元の点ごとの Hom 後合成を主 end の全自然な射にする。
規約：HA §4.2.1、元の全作用。使われ方：同じ通常関手の構成。 -/
def moduleCotensorMap (K : Complex A) {M N : ModuleCategory A D} (f : M ⟶ N) :
    moduleCotensor A D K M ⟶ moduleCotensor A D K N :=
  moduleMorphismMk A D (fun x => homPostcompose K ((moduleEvaluation A D x.unop).map f))
    (moduleCotensorMap_naturality A D K f)

/-- 概要：同じ cotensor 射は点ごとに元の Hom 後合成。
方針：主 end で構成した射の評価の法則を使う。
規約：HA §4.2.1、同じ鎖写像。使われ方：単位・合成・台との比較。 -/
lemma moduleCotensorMap_eval (K : Complex A) {M N : ModuleCategory A D}
    (f : M ⟶ N) (x : D) :
    (moduleEvaluation A D x).map (moduleCotensorMap A D K f) =
      homPostcompose K ((moduleEvaluation A D x).map f) :=
  moduleMorphismMk_eval A D _ _ x

/-- 概要：同じ K による cotensor は元の主加群圏の全関手。
方針：射を全自然な Hom 後合成で送り、評価の忠実性で法則を照合する。
規約：HA §4.2.1、モデル構造の入力なし。使われ方：同じ全対象の frame 候補。 -/
def moduleCotensorFunctor (K : Complex A) : ModuleCategory A D ⥤ ModuleCategory A D where
  obj := moduleCotensor A D K
  map := moduleCotensorMap A D K
  map_id M := by
    apply moduleMorphism_ext
    intro x
    rw [moduleCotensorMap_eval, CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
    rw [← complexHomWhiskerLeft, eHomWhiskerLeft_id]
    rfl
  map_comp f g := by
    apply moduleMorphism_ext
    intro x
    rw [moduleCotensorMap_eval, CategoryTheory.Functor.map_comp,
      CategoryTheory.Functor.map_comp, moduleCotensorMap_eval, moduleCotensorMap_eval]
    rw [← complexHomWhiskerLeft, ← complexHomWhiskerLeft, ← complexHomWhiskerLeft,
      eHomWhiskerLeft_comp]

/-- 概要：同じ cotensor 関手の評価は全関手として通常 Hom と一致。
方針：同じ対象・射の評価式で関手を外延的に照合する。
規約：HA §4.2.1、全通常射。使われ方：実モデルの台での frame 判定。 -/
lemma moduleCotensorFunctor_evaluation (K : Complex A) (x : D) :
    moduleCotensorFunctor A D K ⋙ moduleEvaluation A D x =
      moduleEvaluation A D x ⋙ (eHomFunctor (Complex A) (Complex A)).obj (op K) := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro M N f
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id, CategoryTheory.Functor.comp_map]
  change (moduleEvaluation A D x).map (moduleCotensorMap A D K f) =
    eHomWhiskerLeft (Complex A) K ((moduleEvaluation A D x).map f)
  rw [moduleCotensorMap_eval, complexHomWhiskerLeft]

end SerrePositivity.EInfinity.Modules
