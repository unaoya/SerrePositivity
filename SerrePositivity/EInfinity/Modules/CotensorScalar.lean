module

public import SerrePositivity.EInfinity.Modules.CotensorPointwise

/-!
# 同じ加群 cotensor の係数複体に対する反変作用

概要：M10 の標準単体の全族へ、元の Hom 前合成を接続する。
方針：既存の cochain 合成の結合則と全作用の外延性を使う。
規約：HA §4.2.1、同じ cotensor 対象・元の閉零射。
使われ方：面・退化を含む同じ加群 simplicial 族の構成。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.EInfinity.Modules
open CategoryTheory MonoidalCategory Opposite HomologicalComplex CochainComplex HomComplex
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 概要：共変 Hom の全次数作用は同じ閉零前合成と可換。
方針：既存の作用公式と cochain 合成の結合則を使う。
規約：HA §4.2.1、余分な符号を付けない。使われ方：cotensor の係数反変性。 -/
lemma homCovariantDG_precomposition {K L : Complex A} (f : K ⟶ L) (P Q : Complex A) :
    (homCovariantDG A L).map P Q ≫ homPostcompose _ (homPrecompose f Q) =
      (homCovariantDG A K).map P Q ≫ homPrecompose (homPrecompose f P) _ := by
  apply chain_ext_apply
  intro p g
  apply Cochain.ext
  intro q r hqr
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  change (((homCovariantDG A L).map P Q).f p g |>.comp
    (Cochain.ofHom (homPrecompose f Q)) (add_zero p)).v q r hqr z =
    ((Cochain.ofHom (homPrecompose f P)).comp
      (((homCovariantDG A K).map P Q).f p g) (zero_add p)).v q r hqr z
  rw [Cochain.comp_zero_cochain_v, Cochain.zero_cochain_comp_v]
  change (homPrecompose f Q).f r
      ((((homCovariantDG A L).map P Q).f p g).v q r hqr z) =
    (((homCovariantDG A K).map P Q).f p g).v q r hqr ((homPrecompose f P).f q z)
  rw [homCovariantDG_map_element, homCovariantDG_map_element]
  exact (Cochain.comp_assoc_of_first_is_zero_cochain (Cochain.ofHom f) z g hqr).symm

variable (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 概要：同じ係数前合成は元の加群の全作用と自然。
方針：同じ共変 Hom の交換式を元の加群作用で前合成する。
規約：HA §4.2.1、元の全 dg 作用。使われ方：係数の射を主 end へ入れる。 -/
lemma moduleCotensorPre_naturality {K L : Complex A} (f : K ⟶ L)
    (M : ModuleCategory A D) (x y : Dᵒᵖ) :
    (dgModuleCotensor A D L (ForgetEnrichment.to (Complex A) M)).map x y ≫
      homPostcompose _ (homPrecompose f ((ForgetEnrichment.to (Complex A) M).obj y)) =
    (dgModuleCotensor A D K (ForgetEnrichment.to (Complex A) M)).map x y ≫
      homPrecompose (homPrecompose f ((ForgetEnrichment.to (Complex A) M).obj x)) _ := by
  change ((ForgetEnrichment.to (Complex A) M).map x y ≫
      (homCovariantDG A L).map _ _) ≫ _ =
    ((ForgetEnrichment.to (Complex A) M).map x y ≫ (homCovariantDG A K).map _ _) ≫ _
  have h := congrArg (fun z => (ForgetEnrichment.to (Complex A) M).map x y ≫ z)
    (homCovariantDG_precomposition A f ((ForgetEnrichment.to (Complex A) M).obj x)
      ((ForgetEnrichment.to (Complex A) M).obj y))
  exact (Category.assoc _ _ _).trans (h.trans (Category.assoc _ _ _).symm)

/-- 概要：同じ係数前合成を閉零加群射として取る。
方針：全作用の自然性から主 end の射を構成する。
規約：HA §4.2.1、同じ Hom 前合成。使われ方：標準単体の面と退化。 -/
def moduleCotensorPreMap {K L : Complex A} (f : K ⟶ L) (M : ModuleCategory A D) :
    moduleCotensor A D L M ⟶ moduleCotensor A D K M :=
  moduleMorphismMk A D
    (fun x => homPrecompose f ((ForgetEnrichment.to (Complex A) M).obj x))
    (moduleCotensorPre_naturality A D f M)

/-- 概要：係数前合成の同じ加群射の評価。
方針：主 end の射の評価式を使う。
規約：HA §4.2.1、同じ鎖写像。使われ方：単位・合成・面の照合。 -/
lemma moduleCotensorPreMap_eval {K L : Complex A} (f : K ⟶ L) (M : ModuleCategory A D)
    (x : D) :
    (moduleEvaluation A D x).map (moduleCotensorPreMap A D f M) =
      homPrecompose f ((moduleEvaluation A D x).obj M) :=
  moduleMorphismMk_eval A D _ _ x

/-- 概要：係数前合成は全ての元の加群射について自然。
方針：同じ Hom の前後合成の交換を評価で照合する。
規約：HA §4.2.1、全通常射。使われ方：cotensor の二変数の族。 -/
def moduleCotensorPreNat {K L : Complex A} (f : K ⟶ L) :
    moduleCotensorFunctor A D L ⟶ moduleCotensorFunctor A D K where
  app := moduleCotensorPreMap A D f
  naturality M N g := by
    apply moduleMorphism_ext
    intro x
    change (moduleEvaluation A D x).map
        (moduleCotensorMap A D L g ≫ moduleCotensorPreMap A D f N) =
      (moduleEvaluation A D x).map
        (moduleCotensorPreMap A D f M ≫ moduleCotensorMap A D K g)
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
      moduleCotensorMap_eval, moduleCotensorMap_eval,
      moduleCotensorPreMap_eval, moduleCotensorPreMap_eval]
    exact homPostcompose_precompose A f ((moduleEvaluation A D x).map g)

/-- 概要：同じ cotensor は係数複体に反変な全関手族。
方針：同じ前合成の単位・逆順の合成を主 end の評価で照合する。
規約：HA §4.2.1、全係数射・全加群射。使われ方：標準単体の全関手的な代入。 -/
def moduleCotensorScalarFunctor : (Complex A)ᵒᵖ ⥤ (ModuleCategory A D ⥤ ModuleCategory A D) where
  obj K := moduleCotensorFunctor A D K.unop
  map f := moduleCotensorPreNat A D f.unop
  map_id K := by
    apply NatTrans.ext
    funext M
    apply moduleMorphism_ext
    intro x
    change (moduleEvaluation A D x).map (moduleCotensorPreMap A D (𝟙 K.unop) M) =
      (moduleEvaluation A D x).map (𝟙 (moduleCotensor A D K.unop M))
    rw [moduleCotensorPreMap_eval, CategoryTheory.Functor.map_id,
      ← complexHomWhiskerRight, eHomWhiskerRight_id]
    rfl
  map_comp f g := by
    apply NatTrans.ext
    funext M
    apply moduleMorphism_ext
    intro x
    change (moduleEvaluation A D x).map (moduleCotensorPreMap A D (g.unop ≫ f.unop) M) =
      (moduleEvaluation A D x).map
        (moduleCotensorPreMap A D f.unop M ≫ moduleCotensorPreMap A D g.unop M)
    rw [moduleCotensorPreMap_eval, CategoryTheory.Functor.map_comp,
      moduleCotensorPreMap_eval, moduleCotensorPreMap_eval, homPrecompose_comp]

end SerrePositivity.EInfinity.Modules
