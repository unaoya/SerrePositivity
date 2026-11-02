module

public import SerrePositivity.DifferentialGraded.Module.Left.CategoryComparison
public import SerrePositivity.DifferentialGraded.Category.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Discrete.Basic
public import SerrePositivity.DifferentialGraded.Complexes.HomLimits
public import SerrePositivity.DifferentialGraded.Module.Basic
public import SerrePositivity.DifferentialGraded.Complexes.Cone
public import SerrePositivity.DifferentialGraded.Functor.QuasiEquivalence
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero
public import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts

/-!
# Module.Hom.HomotopyAndOperations

## 概要
Hom end のホモトピーと零・自由・cone・shift・直和および射の操作をまとめる。

## 方針
依存順に連結し、宣言と証明を保存する。

## 規約
元ごとの section で variable と option を保持する。private 名の変更は private_renames で明示する。

## 使われ方
DG の土台とその下流から import する。
-/

/-! ## Homotopy（旧 SerrePositivity/DifferentialGraded/Module/Homotopy.lean） -/

/-! # 全次数 Hom end の境界による加群ホモトピーと K(D)

次数 −1 の要素を Hom end 内に取るため、全 dg 作用との自然性も要求する。
対象ごとに独立した chain homotopy の存在だけでは代用しない。
-/

@[expose] public section Homotopy
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 全 dg 自然な次数 −1 の要素で、その微分が閉零射の差となるもの。 -/
def ModuleHomotopy {M N : ModuleCategory A D} (f g : M ⟶ N) :=
  { h : (homObject A (RightModule A D) M N).X (-1) //
    (homObject A (RightModule A D) M N).d (-1) 0 h =
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) f)).val -
        (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) g)).val }

lemma moduleHomotopy_nonempty_iff {M N : ModuleCategory A D} (f g : M ⟶ N) :
    Nonempty (ModuleHomotopy A D f g) ↔ boundaryRelation A (RightModule A D) f g := by
  rw [boundaryRelation, unit_homotopy_boundary]
  exact ⟨fun ⟨h⟩ => ⟨h.val, h.property⟩, fun ⟨h, dh⟩ => ⟨⟨h, dh⟩⟩⟩

/-- K(D) は主加群 dg 圏の H⁰、すなわち全 dg 自然な境界による商。 -/
abbrev ModuleHomotopyCategory := HomotopyCategory A (RightModule A D)

/-- 閉零加群圏から K(D) への A 線形な商関手。 -/
abbrev moduleToHomotopy : ModuleCategory A D ⥤ ModuleHomotopyCategory A D :=
  toHomotopy A (RightModule A D)

lemma moduleToHomotopy_map_eq_iff {M N : ModuleCategory A D} (f g : M ⟶ N) :
    (moduleToHomotopy A D).map f = (moduleToHomotopy A D).map g ↔
      Nonempty (ModuleHomotopy A D f g) := by
  rw [toHomotopy_map_eq_iff, moduleHomotopy_nonempty_iff]

/-- 加群ホモトピーは、すべての評価で既存 chain homotopy を与える。 -/
lemma moduleHomotopy_evaluation {M N : ModuleCategory A D} {f g : M ⟶ N}
    (h : ModuleHomotopy A D f g) (x : D) :
    Nonempty (Homotopy ((moduleEvaluation A D x).map f)
      ((moduleEvaluation A D x).map g)) := by
  have hb := (moduleHomotopy_nonempty_iff A D f g).1 ⟨h⟩
  have he := (moduleEvaluationDG A D x).preserves_boundary f g hb
  exact (complex_boundary_iff A _ _ _ _).1 he

/-- K(D) の評価を既存の複体ホモトピー圏へ降ろす。 -/
def moduleHomotopyEvaluation (x : D) : ModuleHomotopyCategory A D ⥤
    _root_.HomotopyCategory (ModuleCat A) (.up ℤ) :=
  CategoryTheory.Quotient.lift _ (moduleEvaluation A D x ⋙
    _root_.HomotopyCategory.quotient (ModuleCat A) (.up ℤ)) (by
      intro M N f g hb
      obtain ⟨h⟩ := (moduleHomotopy_nonempty_iff A D f g).2 hb
      obtain ⟨he⟩ := moduleHomotopy_evaluation A D h x
      exact _root_.HomotopyCategory.eq_of_homotopy _ _ he)

lemma moduleHomotopyEvaluation_fac (x : D) :
    moduleToHomotopy A D ⋙ moduleHomotopyEvaluation A D x =
      moduleEvaluation A D x ⋙ _root_.HomotopyCategory.quotient (ModuleCat A) (.up ℤ) :=
  CategoryTheory.Quotient.lift_spec _ _ _

end SerrePositivity.DifferentialGraded
end

end Homotopy

/-! ## QuasiIso（旧 SerrePositivity/DifferentialGraded/Module/QuasiIso.lean） -/

/-! # 右 dg 加群の objectwise 準同型

局所化する射のクラスを Mathlib の MorphismProperty として固定する。
任意可換環上の非有界複体を評価し、モデル構造の存在を仮定しない。
-/

@[expose] public section QuasiIso
universe u v

noncomputable section
namespace SerrePositivity.DifferentialGraded
open CategoryTheory HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 各対象での評価が既存複体の quasiIso となる閉次数零射。 -/
def moduleQuasiIso : MorphismProperty (ModuleCategory A D) :=
  fun _ _ f => ∀ x : D, QuasiIso ((moduleEvaluation A D x).map f)

@[simp]
lemma moduleQuasiIso_iff {M N : ModuleCategory A D} (f : M ⟶ N) :
    moduleQuasiIso A D f ↔ ∀ x : D, QuasiIso ((moduleEvaluation A D x).map f) := Iff.rfl

/-- 指定評価への quasiIso の逆像すべての共通部分。 -/
lemma moduleQuasiIso_eq_iInf : moduleQuasiIso A D =
    ⨅ x : D, (HomologicalComplex.quasiIso (ModuleCat A) (.up ℤ)).inverseImage
      (moduleEvaluation A D x) := by
  ext M N f
  simp [moduleQuasiIso, MorphismProperty.iInf_iff, MorphismProperty.inverseImage]

instance moduleQuasiIsoIsMultiplicative : (moduleQuasiIso A D).IsMultiplicative where
  id_mem M x := by
    rw [CategoryTheory.Functor.map_id]
    infer_instance
  comp_mem f g hf hg x := by
    have := hf x
    have := hg x
    rw [CategoryTheory.Functor.map_comp]
    infer_instance

instance moduleQuasiIsoHasTwoOutOfThree : (moduleQuasiIso A D).HasTwoOutOfThreeProperty where
  of_postcomp f g hg hfg x := by
    have := hg x
    have : QuasiIso ((moduleEvaluation A D x).map f ≫
        (moduleEvaluation A D x).map g) := by
      simpa only [← CategoryTheory.Functor.map_comp] using hfg x
    exact quasiIso_of_comp_right ((moduleEvaluation A D x).map f)
      ((moduleEvaluation A D x).map g)
  of_precomp f g hf hfg x := by
    have := hf x
    have : QuasiIso ((moduleEvaluation A D x).map f ≫
        (moduleEvaluation A D x).map g) := by
      simpa only [← CategoryTheory.Functor.map_comp] using hfg x
    exact quasiIso_of_comp_left ((moduleEvaluation A D x).map f)
      ((moduleEvaluation A D x).map g)

instance moduleQuasiIsoStableUnderRetracts : (moduleQuasiIso A D).IsStableUnderRetracts where
  of_retract h hg x := by
    have := hg x
    exact quasiIso_of_retractArrow (h.map (moduleEvaluation A D x))

instance moduleQuasiIsoRespectsIso : (moduleQuasiIso A D).RespectsIso := by
  rw [moduleQuasiIso_eq_iInf]
  infer_instance

/-- objectwise な判定はすべての評価関手が指定射を送ることと同じ。 -/
lemma moduleQuasiIso_evaluation (x : D) : moduleQuasiIso A D ≤
    (HomologicalComplex.quasiIso (ModuleCat A) (.up ℤ)).inverseImage
      (moduleEvaluation A D x) := fun _ _ _ hf => hf x

/-- 全 dg 自然な加群ホモトピーはすべての評価ホモロジー写像を同一視する。 -/
lemma moduleHomotopy_homologyMap_eq {M N : ModuleCategory A D} {f g : M ⟶ N}
    (h : ModuleHomotopy A D f g) (x : D) (i : ℤ) :
    homologyMap ((moduleEvaluation A D x).map f) i =
      homologyMap ((moduleEvaluation A D x).map g) i :=
  (moduleHomotopy_evaluation A D h x).some.homologyMap_eq i

/-- 指定する quasiIso のクラスは加群ホモトピーで不変。 -/
lemma moduleQuasiIso_iff_of_homotopy {M N : ModuleCategory A D} {f g : M ⟶ N}
    (h : ModuleHomotopy A D f g) : moduleQuasiIso A D f ↔ moduleQuasiIso A D g := by
  simp only [moduleQuasiIso_iff, quasiIso_iff, quasiIsoAt_iff_isIso_homologyMap]
  apply forall_congr'
  intro x
  apply forall_congr'
  intro i
  rw [moduleHomotopy_homologyMap_eq A D h x i]

/-- K(D) で同じ射を表す閉零射は同じ quasiIso 判定を持つ。 -/
lemma moduleQuasiIso_iff_of_homotopy_map_eq {M N : ModuleCategory A D} {f g : M ⟶ N}
    (h : (moduleToHomotopy A D).map f = (moduleToHomotopy A D).map g) :
    moduleQuasiIso A D f ↔ moduleQuasiIso A D g := by
  obtain ⟨hh⟩ := (moduleToHomotopy_map_eq_iff A D f g).1 h
  exact moduleQuasiIso_iff_of_homotopy A D hh

end SerrePositivity.DifferentialGraded
end

end QuasiIso

/-! ## Underlying（旧 SerrePositivity/DifferentialGraded/Module/Underlying.lean） -/

/-! # dg 加群の underlying family

忘却先は対象の離散族。全次数の作用と自然性を捨てる忘却関手であり、
dg 加群そのものを通常の Dᵒᵖ の関手圏と同一視しない。
-/

@[expose] public section Underlying
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 閉零加群の射は全対象の chain map 成分で判定できる。 -/
lemma moduleMorphism_ext {M N : ModuleCategory A D} {f g : M ⟶ N}
    (h : ∀ x : D, (moduleEvaluation A D x).map f = (moduleEvaluation A D x).map g) :
    f = g := by
  change ForgetEnrichment.homTo (Complex A) f = ForgetEnrichment.homTo (Complex A) g
  apply moduleHom_ext
  intro x
  exact (complexClosedHomEquiv A _ _).injective (h x)

/-- 右 dg 加群を対象の離散族に忘却する関手。 -/
def moduleUnderlying : ModuleCategory A D ⥤ (Discrete D ⥤ Complex A) where
  obj M := Discrete.functor (fun x => (moduleEvaluation A D x).obj M)
  map f := Discrete.natTrans (fun x => (moduleEvaluation A D x.as).map f)
  map_id M := by
    apply NatTrans.ext
    funext x
    exact (moduleEvaluation A D x.as).map_id M
  map_comp f g := by
    apply NatTrans.ext
    funext x
    exact (moduleEvaluation A D x.as).map_comp f g

/-- underlying family への忘却は忠実。 -/
instance moduleUnderlying_faithful : (moduleUnderlying A D).Faithful where
  map_injective := by
    intro M N f g h
    apply moduleMorphism_ext
    intro x
    exact congrArg (fun t => t.app (Discrete.mk x)) h
end SerrePositivity.DifferentialGraded
end

end Underlying

/-! ## ClosedMaps（旧 SerrePositivity/DifferentialGraded/Module/ClosedMaps.lean） -/

/-! # 全次数自然な chain map 族から閉零加群射を構成する -/

@[expose] public section ClosedMaps
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D]

/-- 閉零射族の全豊穣自然性は Hom chain map の可換式で検証できる。 -/
lemma closedFamily_naturality {M N : RightModule A D}
    (a : ∀ x : Dᵒᵖ, M.obj x ⟶ N.obj x)
    (h : ∀ x y : Dᵒᵖ, M.map x y ≫ homPostcompose (M.obj x) (a y) =
      N.map x y ≫ homPrecompose (a x) (N.obj y)) (x y : Dᵒᵖ) :
    (β_ (𝟙_ (Complex A)) (x ⟶[Complex A] y)).hom ≫
      (M.map x y ⊗ₘ closedMap A (a y)) ≫ enrichedComposition _ _ _ =
      (closedMap A (a x) ⊗ₘ N.map x y) ≫ enrichedComposition _ _ _ := by
  apply (cancel_epi (λ_ (x ⟶[Complex A] y)).inv).1
  rw [braiding_tensorUnit_left]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [rightUnitor_inv_comp_tensorHom_assoc, leftUnitor_inv_comp_tensorHom_assoc]
  rw [← homPostcompose_closedMap, ← homPrecompose_closedMap]
  exact h x y

/-- 全豊穣自然性から Hom chain map の可換式を復元する。 -/
lemma closedFamily_naturality_converse {M N : RightModule A D}
    (a : ∀ x : Dᵒᵖ, M.obj x ⟶ N.obj x)
    (h : ∀ x y : Dᵒᵖ,
      (β_ (𝟙_ (Complex A)) (x ⟶[Complex A] y)).hom ≫
        (M.map x y ⊗ₘ closedMap A (a y)) ≫ enrichedComposition _ _ _ =
        (closedMap A (a x) ⊗ₘ N.map x y) ≫ enrichedComposition _ _ _) (x y : Dᵒᵖ) :
    M.map x y ≫ homPostcompose (M.obj x) (a y) =
      N.map x y ≫ homPrecompose (a x) (N.obj y) := by
  have hh := congrArg (fun f => (λ_ (x ⟶[Complex A] y)).inv ≫ f) (h x y)
  rw [braiding_tensorUnit_left] at hh
  simp only [Category.assoc, Iso.inv_hom_id_assoc] at hh
  rw [rightUnitor_inv_comp_tensorHom_assoc, leftUnitor_inv_comp_tensorHom_assoc,
    ← homPostcompose_closedMap, ← homPrecompose_closedMap] at hh
  exact hh

/-- 単位パラメータの全次数自然変換の通常 chain map 成分。 -/
abbrev closedTransApp {M N : RightModule A D}
    (τ : ModuleParamTrans A D (𝟙_ (Complex A)) M N) (x : Dᵒᵖ) : M.obj x ⟶ N.obj x :=
  mapFromUnit A (M.obj x) (N.obj x) (τ.app x)

/-- 通常 chain map として読んだ成分も全次数 Hom に関して自然。 -/
lemma closedTransApp_naturality {M N : RightModule A D}
    (τ : ModuleParamTrans A D (𝟙_ (Complex A)) M N) (x y : Dᵒᵖ) :
    M.map x y ≫ homPostcompose (M.obj x) (closedTransApp A τ y) =
      N.map x y ≫ homPrecompose (closedTransApp A τ x) (N.obj y) := by
  apply closedFamily_naturality_converse A (M := M) (N := N)
    (closedTransApp A τ) (fun x y => ?_) x y
  have hx := closedMap_mapFromUnit A (M.obj x) (N.obj x) (τ.app x)
  have hy := closedMap_mapFromUnit A (M.obj y) (N.obj y) (τ.app y)
  change closedMap A (closedTransApp A τ x) = τ.app x at hx
  change closedMap A (closedTransApp A τ y) = τ.app y at hy
  rw [hx, hy]
  exact τ.naturality x y

/-- 全次数自然な通常 chain map 族を単位パラメータの豊穣自然変換にする。 -/
def closedFamilyTrans {M N : RightModule A D}
    (a : ∀ x : Dᵒᵖ, M.obj x ⟶ N.obj x)
    (h : ∀ x y : Dᵒᵖ, M.map x y ≫ homPostcompose (M.obj x) (a y) =
      N.map x y ≫ homPrecompose (a x) (N.obj y)) :
    ModuleParamTrans A D (𝟙_ (Complex A)) M N where
  app x := closedMap A (a x)
  naturality := closedFamily_naturality A (M := M) (N := N) a h

/-- Hom chain map の全次数可換式を作用上で評価する。 -/
lemma closedFamily_action {M N : RightModule A D}
    (a : ∀ x : Dᵒᵖ, M.obj x ⟶ N.obj x)
    (h : ∀ x y : Dᵒᵖ, M.map x y ≫ homPostcompose (M.obj x) (a y) =
      N.map x y ≫ homPrecompose (a x) (N.obj y))
    (x y : Dᵒᵖ) (p r n : ℤ) (hn : r + p = n)
    (f : GradedHom A x y p) (v : (M.obj x).X r) :
    (a y).f n (moduleAction A M f v hn) =
      moduleAction A N f ((a x).f r v) hn := by
  have hh := congrArg (fun t => t.f p f) (h x y)
  change (((M.map x y).f p f).comp (Cochain.ofHom (a y)) (add_zero p)) =
    (Cochain.ofHom (a x)).comp ((N.map x y).f p f) (zero_add p) at hh
  have hv := congrArg (fun c => c.v r n hn v) hh
  rw [Cochain.comp_zero_cochain_v, Cochain.zero_cochain_comp_v,
    Cochain.ofHom_v, Cochain.ofHom_v] at hv
  exact hv

/-- 全次数作用の可換式から Hom chain map の可換式を復元する。 -/
lemma closedFamily_of_action {M N : RightModule A D}
    (a : ∀ x : Dᵒᵖ, M.obj x ⟶ N.obj x)
    (h : ∀ (x y : Dᵒᵖ) (p r n : ℤ) (hn : r + p = n)
      (f : GradedHom A x y p) (v : (M.obj x).X r),
      (a y).f n (moduleAction A M f v hn) =
        moduleAction A N f ((a x).f r v) hn) (x y : Dᵒᵖ) :
    M.map x y ≫ homPostcompose (M.obj x) (a y) =
      N.map x y ≫ homPrecompose (a x) (N.obj y) := by
  apply HomologicalComplex.Hom.ext
  funext p
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro f
  change (((M.map x y).f p f).comp (Cochain.ofHom (a y)) (add_zero p)) =
    (Cochain.ofHom (a x)).comp ((N.map x y).f p f) (zero_add p)
  apply Cochain.ext
  intro r n hn
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro v
  rw [Cochain.comp_zero_cochain_v, Cochain.zero_cochain_comp_v,
    Cochain.ofHom_v, Cochain.ofHom_v]
  exact h x y p r n hn f v

variable (D) [Small.{u} D]
/-- 全次数自然な chain map 族を主 Hom end の閉零加群射へ持ち上げる。 -/
def moduleMorphismMk {M N : RightModule A D}
    (a : ∀ x : Dᵒᵖ, M.obj x ⟶ N.obj x)
    (h : ∀ x y : Dᵒᵖ, M.map x y ≫ homPostcompose (M.obj x) (a y) =
      N.map x y ≫ homPrecompose (a x) (N.obj y)) :
    ForgetEnrichment.of (Complex A) M ⟶ ForgetEnrichment.of (Complex A) N :=
  ForgetEnrichment.homOf (Complex A) (C := RightModule A D) (X := M) (Y := N)
    ((moduleHomEquiv A D (𝟙_ (Complex A)) M N).symm
      (closedFamilyTrans A (M := M) (N := N) a h))

/-- 構成した加群射を評価すると元の chain map 成分に戻る。 -/
@[simp]
lemma moduleMorphismMk_eval {M N : RightModule A D}
    (a : ∀ x : Dᵒᵖ, M.obj x ⟶ N.obj x)
    (h : ∀ x y : Dᵒᵖ, M.map x y ≫ homPostcompose (M.obj x) (a y) =
      N.map x y ≫ homPrecompose (a x) (N.obj y)) (x : D) :
    (moduleEvaluation A D x).map (moduleMorphismMk A D (M := M) (N := N) a h) = a (op x) := by
  let c := closedFamilyTrans A (M := M) (N := N) a h
  have hp := moduleHomEquiv_symm_π A D (𝟙_ (Complex A)) M N c x
  have he := congrArg (fun t : 𝟙_ (Complex A) ⟶ homComplex A (M.obj (op x)) (N.obj (op x)) =>
    complexClosedHomEquiv A (M.obj (op x)) (N.obj (op x))
      (ForgetEnrichment.homOf (Complex A) (C := Complex A)
        (X := M.obj (op x)) (Y := N.obj (op x)) t)) hp
  calc
    _ = complexClosedHomEquiv A (M.obj (op x)) (N.obj (op x))
        (ForgetEnrichment.homOf (Complex A) (C := Complex A)
          (X := M.obj (op x)) (Y := N.obj (op x))
          ((moduleHomEquiv A D (𝟙_ (Complex A)) M N).symm c ≫
            moduleHomπ A D M N x)) := rfl
    _ = complexClosedHomEquiv A (M.obj (op x)) (N.obj (op x))
        (ForgetEnrichment.homOf (Complex A) (C := Complex A)
          (X := M.obj (op x)) (Y := N.obj (op x)) (c.app (op x))) := he
    _ = a (op x) := Equiv.apply_symm_apply (complexClosedHomEquiv A _ _) _
/-- 全次数の Hom 可換式を持つ通常 chain map 族。 -/
abbrev ModuleMapFamily (M N : RightModule A D) :=
  { a : ∀ x : Dᵒᵖ, M.obj x ⟶ N.obj x //
    ∀ x y : Dᵒᵖ, M.map x y ≫ homPostcompose (M.obj x) (a y) =
      N.map x y ≫ homPrecompose (a x) (N.obj y) }

/-- 閉零自然変換として読んだ加群射の成分は評価関手の射。 -/
lemma moduleClosedHomEquiv_app {M N : ModuleCategory A D} (f : M ⟶ N) (x : D) :
    closedTransApp A (moduleClosedHomEquiv A D M N f) (op x) =
      (moduleEvaluation A D x).map f := rfl

/-- 主 end の閉零射と全次数自然な chain map 族の同値。 -/
def moduleMapFamilyEquiv (M N : ModuleCategory A D) :
    (M ⟶ N) ≃ ModuleMapFamily A D (ForgetEnrichment.to (Complex A) M)
      (ForgetEnrichment.to (Complex A) N) where
  toFun f := ⟨closedTransApp A (moduleClosedHomEquiv A D M N f),
    closedTransApp_naturality A (moduleClosedHomEquiv A D M N f)⟩
  invFun a := moduleMorphismMk A D a.val a.property
  left_inv f := by
    apply moduleMorphism_ext
    intro x
    rw [moduleMorphismMk_eval]
    exact moduleClosedHomEquiv_app A D f x
  right_inv a := by
    apply Subtype.ext
    funext x
    change closedTransApp A (moduleClosedHomEquiv A D M N
      (moduleMorphismMk A D a.val a.property)) x = a.val x
    rw [moduleClosedHomEquiv_app A D _ x.unop, moduleMorphismMk_eval]
end SerrePositivity.DifferentialGraded
end

end ClosedMaps

/-! ## Zero（旧 SerrePositivity/DifferentialGraded/Module/Zero.lean） -/

/-! # 全次数の零加群と閉零加群圏の零対象 -/

@[expose] public section Zero
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits MonoidalCategory Opposite
open scoped ZeroObject
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]

/-- 各対象で零複体、全次数の Hom 作用で零となる右 dg 加群。 -/
abbrev zeroModule : RightModule A D where
  obj _ := 0
  map _ _ := 0
  map_id _ := (homComplex_isZero_src (isZero_zero (Complex A))).eq_of_tgt _ _
  map_comp _ _ _ := (homComplex_isZero_src (isZero_zero (Complex A))).eq_of_tgt _ _

/-- 零加群の対象での評価は零複体。 -/
lemma zeroModule_obj (x : Dᵒᵖ) : (zeroModule A D).obj x = (0 : Complex A) := rfl

variable [Small.{u} D]

/-- objectwise 零加群からの Hom end 自体が零複体になる。 -/
lemma moduleHom_isZero_src (M N : RightModule A D)
    (hM : ∀ x : D, IsZero (M.obj (op x))) : IsZero (moduleHom A D M N) := by
  apply (IsZero.iff_id_eq_zero _).2
  apply moduleHom_ext
  intro x
  exact (homComplex_isZero_src (hM x)).eq_of_tgt _ _

/-- objectwise 零加群への Hom end 自体が零複体になる。 -/
lemma moduleHom_isZero_tgt (M N : RightModule A D)
    (hN : ∀ x : D, IsZero (N.obj (op x))) : IsZero (moduleHom A D M N) := by
  apply (IsZero.iff_id_eq_zero _).2
  apply moduleHom_ext
  intro x
  exact (homComplex_isZero_tgt (hN x)).eq_of_tgt _ _

/-- 閉次数零加群圏に置いた具体的零加群。 -/
abbrev moduleZero : ModuleCategory A D := ForgetEnrichment.of (Complex A) (zeroModule A D)

/-- 全次数自然性を保持した零加群からの射。 -/
def moduleZeroTo (M : ModuleCategory A D) : moduleZero A D ⟶ M :=
  moduleMorphismMk A D (M := zeroModule A D)
    (N := ForgetEnrichment.to (Complex A) M) (fun _ => 0)
    (fun _ _ => (homComplex_isZero_src (isZero_zero (Complex A))).eq_of_tgt _ _)

/-- 全次数自然性を保持した零加群への射。 -/
def moduleToZero (M : ModuleCategory A D) : M ⟶ moduleZero A D :=
  moduleMorphismMk A D (M := ForgetEnrichment.to (Complex A) M)
    (N := zeroModule A D) (fun _ => 0)
    (fun _ _ => (homComplex_isZero_tgt (isZero_zero (Complex A))).eq_of_tgt _ _)

/-- 零加群からの射は各評価で零 chain map。 -/
@[simp] lemma moduleZeroTo_eval (M : ModuleCategory A D) (x : D) :
    (moduleEvaluation A D x).map (moduleZeroTo A D M) = 0 :=
  moduleMorphismMk_eval A D _ _ x

/-- 零加群への射は各評価で零 chain map。 -/
@[simp] lemma moduleToZero_eval (M : ModuleCategory A D) (x : D) :
    (moduleEvaluation A D x).map (moduleToZero A D M) = 0 :=
  moduleMorphismMk_eval A D _ _ x

/-- 具体的零加群は閉零圏の零対象の普遍性を満たす。 -/
lemma moduleZero_isZero : IsZero (moduleZero A D) := by
  constructor
  · intro M
    refine ⟨⟨⟨moduleZeroTo A D M⟩, fun f => ?_⟩⟩
    apply moduleMorphism_ext
    intro x
    exact (isZero_zero (Complex A)).eq_of_src _ _
  · intro M
    refine ⟨⟨⟨moduleToZero A D M⟩, fun f => ?_⟩⟩
    apply moduleMorphism_ext
    intro x
    exact (isZero_zero (Complex A)).eq_of_tgt _ _

instance moduleHasZeroObject : HasZeroObject (ModuleCategory A D) :=
  (moduleZero_isZero A D).hasZeroObject

/-- 各評価は加法的であり、零射を保存する。 -/
instance moduleEvaluationAdditive (x : D) : (moduleEvaluation A D x).Additive := by
  change ((moduleEvaluationDG A D x).onClosed ⋙ closedToComplex A).Additive
  infer_instance

/-- 零対象性は全対象での零複体性と同値。 -/
lemma module_isZero_iff (M : ModuleCategory A D) :
    IsZero M ↔ ∀ x : D, IsZero ((moduleEvaluation A D x).obj M) := by
  constructor
  · intro h x
    exact (moduleEvaluation A D x).map_isZero h
  · intro h
    apply (IsZero.iff_id_eq_zero M).2
    apply moduleMorphism_ext
    intro x
    rw [CategoryTheory.Functor.map_id, Functor.map_zero]
    exact (h x).eq_of_src _ _

/-- 選ばれた圏の零対象を評価すると零複体に標準的に同型。 -/
def moduleEvaluationZeroIso (x : D) :
    (moduleEvaluation A D x).obj (0 : ModuleCategory A D) ≅ (0 : Complex A) :=
  ((moduleEvaluation A D x).map_isZero (isZero_zero (ModuleCategory A D))).isoZero
end SerrePositivity.DifferentialGraded
end

end Zero

/-! ## Free（旧 SerrePositivity/DifferentialGraded/Module/Free.lean） -/

/-! # 自由右 dg 加群の関手性 -/

@[expose] public section Free
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory Opposite
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D] [Small.{u} D]

/-- 左 tensor の因子の chain map を全次数自然な加群射へ持ち上げる。 -/
def tensorModuleMap {K L : Complex A} (g : K ⟶ L) (M : RightModule A D) :
    ForgetEnrichment.of (Complex A) (tensorModule K M) ⟶
      ForgetEnrichment.of (Complex A) (tensorModule L M) :=
  moduleMorphismMk A D (M := tensorModule K M) (N := tensorModule L M)
    (fun x => g ⊗ₘ 𝟙 (M.obj x)) (by
      intro x y
      change (M.map x y ≫ tensorLeftHom K (M.obj x) (M.obj y)) ≫
          homPostcompose (K ⊗ M.obj x) (g ⊗ₘ 𝟙 (M.obj y)) =
        (M.map x y ≫ tensorLeftHom L (M.obj x) (M.obj y)) ≫
          homPrecompose (g ⊗ₘ 𝟙 (M.obj x)) (L ⊗ M.obj y)
      rw [Category.assoc, Category.assoc, tensorLeftHom_naturality])

/-- tensor 因子から持ち上げた加群射の成分。 -/
@[simp]
lemma tensorModuleMap_eval {K L : Complex A} (g : K ⟶ L) (M : RightModule A D) (x : D) :
    (moduleEvaluation A D x).map (tensorModuleMap g M) = g ⊗ₘ 𝟙 (M.obj (op x)) :=
  moduleMorphismMk_eval A D _ _ x

/-- 固定した右加群 M への左 tensor を複体の関手にする。 -/
@[implicit_reducible]
def tensorModuleFunctor (M : RightModule A D) : Complex A ⥤ ModuleCategory A D where
  obj K := ForgetEnrichment.of (Complex A) (tensorModule K M)
  map g := tensorModuleMap g M
  map_id K := by
    apply moduleMorphism_ext
    intro x
    rw [CategoryTheory.Functor.map_id, tensorModuleMap_eval]
    simp
    rfl
  map_comp g h := by
    apply moduleMorphism_ext
    intro x
    rw [CategoryTheory.Functor.map_comp, tensorModuleMap_eval, tensorModuleMap_eval,
      tensorModuleMap_eval]
    simp only [tensorHom_comp_tensorHom, Category.id_comp]

/-- x において複体 K で生成する自由右加群関手。 -/
abbrev freeAt (x : D) : Complex A ⥤ ModuleCategory A D :=
  tensorModuleFunctor (representable A x)

/-- 自由加群関手の対象成分は指定した tensor。 -/
lemma freeAt_obj (x y : D) (K : Complex A) :
    (moduleEvaluation A D y).obj ((freeAt x).obj K) = K ⊗ (y ⟶[Complex A] x) := rfl
end SerrePositivity.DifferentialGraded
end

end Free

/-! ## Cone（旧 SerrePositivity/DifferentialGraded/Module/Cone.lean） -/

/-! # 全次数作用を持つ右 dg 加群の cone 対象 -/

@[expose] public section Cone
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D]

/-- 加群作用は閉単位を恒等 cochain に移す。 -/
lemma moduleMap_unit_cochain (M : RightModule A D) (x : Dᵒᵖ) :
    (M.map x x).f 0 (unitElement A x).val = Cochain.ofHom (𝟙 (M.obj x)) := by
  have h := congrArg (fun f => (cycleFromUnit _ f).val) (M.toFunctor.map_id x)
  rw [cycleFromUnit_postcomp] at h
  change (M.map x x).f 0 (unitElement A x).val =
    (cycleFromUnit _ (identity (M.obj x))).val at h
  simpa only [identity, cycleFromUnit_unitFromCycle] using h

/-- 加群作用の豊穣順合成を cochain 全体で読む。 -/
lemma moduleMap_forward (M : RightModule A D) {x y z : Dᵒᵖ} {p q n : ℤ}
    (f : GradedHom A x y p) (g : GradedHom A y z q) (hn : p + q = n) :
    (M.map x z).f n (forward A f g hn) =
      (p * q).negOnePow • ((M.map x y).f p f).comp ((M.map y z).f q g) hn := by
  have h := congrArg (fun l => l.f n
    (ιTensorObj (x ⟶[Complex A] y) (y ⟶[Complex A] z) p q n hn (f ⊗ₜ[A] g)))
    (M.toFunctor.map_comp x y z)
  change (M.map x z).f n (forward A f g hn) =
    (enrichedComposition _ _ _).f n
      ((M.map x y ⊗ₘ M.map y z).f n
        (ιTensorObj (x ⟶[Complex A] y) (y ⟶[Complex A] z) p q n hn (f ⊗ₜ[A] g))) at h
  rw [tensorMap_apply, enrichedComposition_apply] at h
  exact h

variable {A}
/-- 全次数自然な閉零射族の objectwise mapping cone とその dg 作用。 -/
abbrev coneModule (M N : RightModule A D)
    (a : ∀ x : Dᵒᵖ, M.obj x ⟶ N.obj x)
    (h : ∀ x y : Dᵒᵖ, M.map x y ≫ homPostcompose (M.obj x) (a y) =
      N.map x y ≫ homPrecompose (a x) (N.obj y)) : RightModule A D where
  obj x := mappingCone (a x)
  map x y := coneHomMap (a x) (a y) (M.map x y) (N.map x y) (h x y)
  map_id x := by
    apply (unitCycleEquiv _).injective
    apply Subtype.ext
    change (cycleFromUnit _ (eId (Complex A) x ≫
      coneHomMap (a x) (a x) (M.map x x) (N.map x x) (h x x))).val =
        (cycleFromUnit _ (identity (mappingCone (a x)))).val
    rw [cycleFromUnit_postcomp]
    change coneMapCochain (a x) (a x)
      ((M.map x x).f 0 (unitElement A x).val) ((N.map x x).f 0 (unitElement A x).val) = _
    rw [moduleMap_unit_cochain, moduleMap_unit_cochain]
    simp only [identity, cycleFromUnit_unitFromCycle]
    exact coneMapCochain_identity (a x)
  map_comp x y z := by
    apply tensorHom_ext
    intro p q n hn
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro f g
    change coneMapCochain (a x) (a z)
      ((M.map x z).f n (forward A f g hn)) ((N.map x z).f n (forward A f g hn)) =
      (enrichedComposition _ _ _).f n
        ((coneHomMap (a x) (a y) (M.map x y) (N.map x y) (h x y) ⊗ₘ
          coneHomMap (a y) (a z) (M.map y z) (N.map y z) (h y z)).f n
            (ιTensorObj (x ⟶[Complex A] y) (y ⟶[Complex A] z) p q n hn (f ⊗ₜ[A] g)))
    rw [tensorMap_apply, enrichedComposition_apply, coneHomMap_apply, coneHomMap_apply,
      moduleMap_forward, moduleMap_forward, coneMapCochain_units_smul,
      coneMapCochain_comp]

variable (A D) [Small.{u} D]
/-- 主閉零加群圏の射の cone。 -/
abbrev moduleCone {M N : ModuleCategory A D} (f : M ⟶ N) : ModuleCategory A D :=
  ForgetEnrichment.of (Complex A) (coneModule (ForgetEnrichment.to (Complex A) M)
    (ForgetEnrichment.to (Complex A) N)
    (closedTransApp A (moduleClosedHomEquiv A D M N f))
    (closedTransApp_naturality A (moduleClosedHomEquiv A D M N f)))

/-- 評価すると既存 Mathlib の mapping cone と同じ複体になる。 -/
lemma moduleCone_eval {M N : ModuleCategory A D} (f : M ⟶ N) (x : D) :
    (moduleEvaluation A D x).obj (moduleCone A D f) =
      mappingCone ((moduleEvaluation A D x).map f) := rfl

/-- cone の標準包含は全次数自然な加群射。 -/
def moduleConeInr {M N : ModuleCategory A D} (f : M ⟶ N) : N ⟶ moduleCone A D f :=
  moduleMorphismMk A D (M := ForgetEnrichment.to (Complex A) N)
    (N := ForgetEnrichment.to (Complex A) (moduleCone A D f))
    (fun x => mappingCone.inr (closedTransApp A (moduleClosedHomEquiv A D M N f) x))
    (fun x y => coneHomMap_inr _ _ _ _
      (closedTransApp_naturality A (moduleClosedHomEquiv A D M N f) x y))

/-- 標準包含の評価は Mathlib の標準包含。 -/
@[simp] lemma moduleConeInr_eval {M N : ModuleCategory A D} (f : M ⟶ N) (x : D) :
    (moduleEvaluation A D x).map (moduleConeInr A D f) =
      mappingCone.inr ((moduleEvaluation A D x).map f) := by
  unfold moduleConeInr
  rw [moduleMorphismMk_eval]
  rfl
end SerrePositivity.DifferentialGraded
end

end Cone

/-! ## ConeDesc（旧 SerrePositivity/DifferentialGraded/Module/ConeDesc.lean） -/

/-! # 合成が零となる加群射の全dg自然なcone延長 -/

@[expose] public section ConeDesc
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory HomologicalComplex CochainComplex HomComplex Opposite
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma moduleCompZero_eval {L M N : ModuleCategory A D} (a : L ⟶ M) (q : M ⟶ N)
    (h : a ≫ q = 0) (x : Dᵒᵖ) :
    closedTransApp A (moduleClosedHomEquiv A D L M a) x ≫
      closedTransApp A (moduleClosedHomEquiv A D M N q) x = 0 := by
  change (moduleEvaluation A D x.unop).map a ≫ (moduleEvaluation A D x.unop).map q = 0
  rw [← CategoryTheory.Functor.map_comp, h, CategoryTheory.Functor.map_zero]

def moduleConeDesc {L M N : ModuleCategory A D} (a : L ⟶ M) (q : M ⟶ N) (h : a ≫ q = 0) :
    moduleCone A D a ⟶ N :=
  moduleMorphismMk A D (M := ForgetEnrichment.to (Complex A) (moduleCone A D a))
    (N := ForgetEnrichment.to (Complex A) N)
    (fun x => complexConeDesc (closedTransApp A (moduleClosedHomEquiv A D L M a) x)
      (closedTransApp A (moduleClosedHomEquiv A D M N q) x) (moduleCompZero_eval A D a q h x)) (by
        intro x y
        apply HomologicalComplex.Hom.ext
        funext p
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro b
        change (coneMapCochain
          (closedTransApp A (moduleClosedHomEquiv A D L M a) x)
          (closedTransApp A (moduleClosedHomEquiv A D L M a) y)
          (((ForgetEnrichment.to (Complex A) L).map x y).f p b)
          (((ForgetEnrichment.to (Complex A) M).map x y).f p b)).comp
          (Cochain.ofHom (complexConeDesc _ _ (moduleCompZero_eval A D a q h y))) (add_zero p) =
          (Cochain.ofHom (complexConeDesc _ _ (moduleCompZero_eval A D a q h x))).comp
            (((ForgetEnrichment.to (Complex A) N).map x y).f p b) (zero_add p)
        apply coneMapCochain_desc
        exact congrArg (fun k => k.f p b)
          (closedTransApp_naturality A (moduleClosedHomEquiv A D M N q) x y))

@[simp] lemma moduleConeDesc_eval {L M N : ModuleCategory A D} (a : L ⟶ M) (q : M ⟶ N)
    (h : a ≫ q = 0) (x : D) :
    (moduleEvaluation A D x).map (moduleConeDesc A D a q h) =
      complexConeDesc ((moduleEvaluation A D x).map a) ((moduleEvaluation A D x).map q)
        (moduleCompZero_eval A D a q h (op x)) := by
  unfold moduleConeDesc
  rw [moduleMorphismMk_eval]
  rfl

@[reassoc] lemma moduleConeDesc_inr {L M N : ModuleCategory A D} (a : L ⟶ M) (q : M ⟶ N)
    (h : a ≫ q = 0) : moduleConeInr A D a ≫ moduleConeDesc A D a q h = q := by
  apply moduleMorphism_ext
  intro x
  rw [CategoryTheory.Functor.map_comp, moduleConeInr_eval, moduleConeDesc_eval, complexConeDesc_inr]

end SerrePositivity.DifferentialGraded
end

end ConeDesc

/-! ## Shift（旧 SerrePositivity/DifferentialGraded/Module/Shift.lean） -/

/-! # 右 dg 加群の整数 shift と objectwise 評価 -/

@[expose] public section Shift
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory Opposite HomologicalComplex CochainComplex HomComplex
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]

/-- 既存複体の shift を全次数 dg 作用へ拡張した右加群。 -/
abbrev shiftModule (s : ℤ) (M : RightModule A D) : RightModule A D where
  obj x := (M.obj x)⟦s⟧
  map x y := M.map x y ≫ shiftHom s (M.obj x) (M.obj y)
  map_id := (DGFunctor.comp M.toFunctor (shiftDG s)).map_id
  map_comp := (DGFunctor.comp M.toFunctor (shiftDG s)).map_comp

/-- 加群 shift は主 dg 関手の合成と同じデータ。 -/
lemma shiftModule_eq_comp (s : ℤ) (M : RightModule A D) :
    (shiftModule s M).toFunctor = DGFunctor.comp M.toFunctor (shiftDG s) := rfl

/-- 全次数右作用の shift の符号と再添字付け。 -/
lemma shiftModule_map_v (s : ℤ) (M : RightModule A D) (x y : Dᵒᵖ)
    (p i j : ℤ) (hij : i + p = j) (f : GradedHom A x y p) :
    (((shiftModule s M).map x y).f p f).v i j hij =
      (s * p).negOnePow • ((M.map x y).f p f).v (i + s) (j + s) (by omega) :=
  shiftHom_v s _ _ p i j hij _

/-- 全次数自然な chain map 族の通常 shift も全次数自然。 -/
lemma shiftedFamily_naturality (s : ℤ) {M N : RightModule A D}
    (a : ∀ x : Dᵒᵖ, M.obj x ⟶ N.obj x)
    (h : ∀ x y : Dᵒᵖ, M.map x y ≫ homPostcompose (M.obj x) (a y) =
      N.map x y ≫ homPrecompose (a x) (N.obj y)) (x y : Dᵒᵖ) :
    (shiftModule s M).map x y ≫
      homPostcompose ((M.obj x)⟦s⟧) ((a y)⟦s⟧') =
    (shiftModule s N).map x y ≫
      homPrecompose ((a x)⟦s⟧') ((N.obj y)⟦s⟧) := by
  apply closedFamily_of_action A (M := shiftModule s M) (N := shiftModule s N)
    (fun x => (a x)⟦s⟧')
  intro x y p r n hn f v
  unfold moduleAction
  rw [shiftModule_map_v, shiftModule_map_v]
  change (a y).f (n + s)
      ((s * p).negOnePow • (((M.map x y).f p f).v (r + s) (n + s) (by omega) v)) =
    (s * p).negOnePow •
      (((N.map x y).f p f).v (r + s) (n + s) (by omega) ((a x).f (r + s) v))
  simp only [Units.smul_def, map_zsmul]
  exact congrArg ((s * p).negOnePow.val • ·)
    (closedFamily_action A a h x y p (r + s) (n + s) (by omega) f v)

variable (A D) [Small.{u} D]

/-- 閉零加群圏の具体的整数 shift。 -/
abbrev moduleShiftObj (s : ℤ) (M : ModuleCategory A D) : ModuleCategory A D :=
  ForgetEnrichment.of (Complex A) (shiftModule s (ForgetEnrichment.to (Complex A) M))

/-- 加群射の shift。成分は Mathlib の chain map shift。 -/
def moduleShiftMap (s : ℤ) {M N : ModuleCategory A D} (f : M ⟶ N) :
    moduleShiftObj A D s M ⟶ moduleShiftObj A D s N :=
  moduleMorphismMk A D
    (M := shiftModule s (ForgetEnrichment.to (Complex A) M))
    (N := shiftModule s (ForgetEnrichment.to (Complex A) N))
    (fun x => (closedTransApp A (moduleClosedHomEquiv A D M N f) x)⟦s⟧')
    (shiftedFamily_naturality s _
      (closedTransApp_naturality A (moduleClosedHomEquiv A D M N f)))

/-- 射の shift の評価は既存 chain map shift と一致する。 -/
@[simp] lemma moduleShiftMap_eval (s : ℤ) {M N : ModuleCategory A D} (f : M ⟶ N) (x : D) :
    (moduleEvaluation A D x).map (moduleShiftMap A D s f) =
      ((moduleEvaluation A D x).map f)⟦s⟧' := by
  unfold moduleShiftMap
  rw [moduleMorphismMk_eval, moduleClosedHomEquiv_app]

/-- 整数ごとの加群 shift 関手。 -/
@[implicit_reducible]
def moduleShiftFunctor (s : ℤ) : ModuleCategory A D ⥤ ModuleCategory A D where
  obj := moduleShiftObj A D s
  map := moduleShiftMap A D s
  map_id M := by
    apply moduleMorphism_ext
    intro x
    simp only [moduleShiftMap_eval, CategoryTheory.Functor.map_id]
    rfl
  map_comp f g := by
    apply moduleMorphism_ext
    intro x
    simp only [moduleShiftMap_eval, CategoryTheory.Functor.map_comp]

/-- 評価は各整数 shift と通常複体の shift の間で可換。 -/
def moduleShiftEvaluationIso (s : ℤ) (x : D) :
    moduleShiftFunctor A D s ⋙ moduleEvaluation A D x ≅
      moduleEvaluation A D x ⋙ CategoryTheory.shiftFunctor (Complex A) s :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro M N f
    change (moduleEvaluation A D x).map (moduleShiftMap A D s f) ≫ 𝟙 _ =
      𝟙 _ ≫ ((moduleEvaluation A D x).map f)⟦s⟧'
    rw [Category.comp_id, Category.id_comp, moduleShiftMap_eval])
end SerrePositivity.DifferentialGraded
end

end Shift

/-! ## LeftZero（旧 SerrePositivity/DifferentialGraded/Module/LeftZero.lean） -/

/-! # 左dg加群圏の零対象と評価による零性の保存 -/

@[expose] public section LeftZero
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 既存左右同値から得られる左加群の具体的零対象。 -/
def leftModuleZero : LeftModuleCategory A D :=
  (leftRightOppositeEquivalence A D).inverse.obj (moduleZero A Dᵒᵖ)

lemma leftModuleZero_isZero : IsZero (leftModuleZero A D) := by
  apply IsZero.of_full_of_faithful_of_isZero (leftModuleToRightOpposite A D)
  exact (moduleZero_isZero A Dᵒᵖ).of_iso
    ((leftRightOppositeEquivalence A D).counitIso.app (moduleZero A Dᵒᵖ))

instance leftModuleHasZeroObject : HasZeroObject (LeftModuleCategory A D) :=
  (leftModuleZero_isZero A D).hasZeroObject

instance leftModuleEvaluationAdditive (x : D) : (leftModuleEvaluation A D x).Additive := by
  change ((leftModuleEvaluationDG A D x).onClosed ⋙ closedToComplex A).Additive
  infer_instance

lemma leftModuleZero_evaluation_isZero (x : D) :
    IsZero ((leftModuleEvaluation A D x).obj (leftModuleZero A D)) :=
  (leftModuleEvaluation A D x).map_isZero (leftModuleZero_isZero A D)

end SerrePositivity.DifferentialGraded
end

end LeftZero

/-! ## LeftQuasiIso（旧 SerrePositivity/DifferentialGraded/Module/LeftQuasiIso.lean） -/

/-! # 左dg加群の指定objectwise quasiIso -/

@[expose] public section LeftQuasiIso
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Opposite HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 既存左右同値による、Dᵒᵖ上の指定準同型クラスの逆像。 -/
def leftModuleQuasiIso : MorphismProperty (LeftModuleCategory A D) :=
  (moduleQuasiIso A Dᵒᵖ).inverseImage (leftModuleToRightOpposite A D)

lemma leftModuleQuasiIso_iff {L L' : LeftModuleCategory A D} (g : L ⟶ L') :
    leftModuleQuasiIso A D g ↔ ∀ x : D, QuasiIso ((leftModuleEvaluation A D x).map g) := by
  change (∀ x : Dᵒᵖ, QuasiIso ((moduleEvaluation A Dᵒᵖ x).map
    ((leftModuleToRightOpposite A D).map g))) ↔ _
  constructor
  · intro h x
    simpa only [leftModuleToRightOpposite_map_eval] using h (op x)
  · intro h x
    obtain ⟨x⟩ := x
    simpa only [leftModuleToRightOpposite_map_eval] using h x

instance leftModuleQuasiIsoIsMultiplicative : (leftModuleQuasiIso A D).IsMultiplicative := by
  dsimp [leftModuleQuasiIso]
  infer_instance

instance leftModuleQuasiIsoHasTwoOutOfThree :
    (leftModuleQuasiIso A D).HasTwoOutOfThreeProperty := by
  dsimp [leftModuleQuasiIso]
  infer_instance

instance leftModuleQuasiIsoStableUnderRetracts :
    (leftModuleQuasiIso A D).IsStableUnderRetracts := by
  dsimp [leftModuleQuasiIso]
  infer_instance

instance leftModuleQuasiIsoRespectsIso : (leftModuleQuasiIso A D).RespectsIso := by
  dsimp [leftModuleQuasiIso]
  infer_instance

end SerrePositivity.DifferentialGraded
end

end LeftQuasiIso

/-! ## LeftQuasiIsoInverse（旧 SerrePositivity/DifferentialGraded/Module/LeftQuasiIsoInverse.lean） -/

/-! # 左右加群同値の逆関手による指定準同型クラスの保存・反映

## 概要
左右加群同値の逆関手による指定準同型クラスの保存・反映。

## 方針
既存の全dg自然なHom・作用・chain mapと局所化の計算を再利用する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanの依存。直接の利用箇所：Tensor/LeftKFlatResolution.lean。dg加群の導来作用・準同値比較の基盤。
任意可換環上のMorita・K理論のモデル比較に再利用できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section LeftQuasiIsoInverse
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Opposite
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma leftRightOpposite_inverse_quasiIso_iff {M N : ModuleCategory A Dᵒᵖ} (f : M ⟶ N) :
    leftModuleQuasiIso A D ((leftRightOppositeEquivalence A D).inverse.map f) ↔
      moduleQuasiIso A Dᵒᵖ f := by
  let E := leftRightOppositeEquivalence A D
  let W := moduleQuasiIso A Dᵒᵖ
  change W (E.functor.map (E.inverse.map f)) ↔ W f
  calc
    W (E.functor.map (E.inverse.map f)) ↔
        W (E.functor.map (E.inverse.map f) ≫ (E.counitIso.app N).hom) :=
      (W.cancel_right_of_respectsIso _ _).symm
    _ ↔ W ((E.counitIso.app M).hom ≫ f) :=
      Iff.of_eq (congrArg (fun k => W k) (E.counitIso.hom.naturality f))
    _ ↔ W f := W.cancel_left_of_respectsIso _ _

end SerrePositivity.DifferentialGraded
end

end LeftQuasiIsoInverse

/-! ## Biproduct（旧 SerrePositivity/DifferentialGraded/Module/Biproduct.lean） -/

/-! # objectwise 二項直和の全次数作用と普遍性 -/

@[expose] public section Biproduct
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits MonoidalCategory Opposite HomologicalComplex CochainComplex HomComplex
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]

/-- 対象での直和に対角の全次数作用を与えた右 dg 加群。 -/
abbrev biprodModule (M N : RightModule A D) : RightModule A D where
  obj x := M.obj x ⊞ N.obj x
  map x y := biprodHomMap (M.map x y) (N.map x y)
  map_id x := by
    change eId (Complex A) x ≫ biprodHomMap (M.map x x) (N.map x x) =
      identity (M.obj x ⊞ N.obj x)
    rw [biprodHomMap_precomp, M.toFunctor.map_id, N.toFunctor.map_id]
    exact biprodHomMap_identity _ _
  map_comp x y z := by
    change eComp (Complex A) x y z ≫ biprodHomMap (M.map x z) (N.map x z) =
      (biprodHomMap (M.map x y) (N.map x y) ⊗ₘ
        biprodHomMap (M.map y z) (N.map y z)) ≫ enrichedComposition _ _ _
    rw [biprodHomMap_precomp, M.toFunctor.map_comp, N.toFunctor.map_comp,
      biprodHomMap_comp]
    rfl

/-- 全次数作用の行列は対角である。 -/
lemma biprodModule_map_v (M N : RightModule A D) (x y : Dᵒᵖ)
    (p i j : ℤ) (hij : i + p = j) (f : GradedHom A x y p) :
    (((biprodModule M N).map x y).f p f).v i j hij =
      (biprod.fst : M.obj x ⊞ N.obj x ⟶ M.obj x).f i ≫
        ((M.map x y).f p f).v i j hij ≫
          (biprod.inl : M.obj y ⟶ M.obj y ⊞ N.obj y).f j +
      (biprod.snd : M.obj x ⊞ N.obj x ⟶ N.obj x).f i ≫
        ((N.map x y).f p f).v i j hij ≫
          (biprod.inr : N.obj y ⟶ M.obj y ⊞ N.obj y).f j :=
  biprodHomMap_v _ _ p i j hij f

variable (A D) [Small.{u} D]

/-- 閉零加群圏の具体的 objectwise 二項直和。 -/
abbrev moduleBiprod (M N : ModuleCategory A D) : ModuleCategory A D :=
  ForgetEnrichment.of (Complex A) (biprodModule
    (ForgetEnrichment.to (Complex A) M) (ForgetEnrichment.to (Complex A) N))

/-- 第一射影は全次数自然な加群射。 -/
def moduleBiprodFst (M N : ModuleCategory A D) : moduleBiprod A D M N ⟶ M :=
  moduleMorphismMk A D
    (M := biprodModule (ForgetEnrichment.to (Complex A) M) (ForgetEnrichment.to (Complex A) N))
    (N := ForgetEnrichment.to (Complex A) M) (fun _ => biprod.fst)
    (fun _ _ => biprodHomMap_fst _ _)

/-- 第二射影は全次数自然な加群射。 -/
def moduleBiprodSnd (M N : ModuleCategory A D) : moduleBiprod A D M N ⟶ N :=
  moduleMorphismMk A D
    (M := biprodModule (ForgetEnrichment.to (Complex A) M) (ForgetEnrichment.to (Complex A) N))
    (N := ForgetEnrichment.to (Complex A) N) (fun _ => biprod.snd)
    (fun _ _ => biprodHomMap_snd _ _)

/-- 第一包含は全次数自然な加群射。 -/
def moduleBiprodInl (M N : ModuleCategory A D) : M ⟶ moduleBiprod A D M N :=
  moduleMorphismMk A D (M := ForgetEnrichment.to (Complex A) M)
    (N := biprodModule (ForgetEnrichment.to (Complex A) M) (ForgetEnrichment.to (Complex A) N))
    (fun _ => biprod.inl)
    (fun _ _ => (biprodHomMap_inl _ _).symm)

/-- 第二包含は全次数自然な加群射。 -/
def moduleBiprodInr (M N : ModuleCategory A D) : N ⟶ moduleBiprod A D M N :=
  moduleMorphismMk A D (M := ForgetEnrichment.to (Complex A) N)
    (N := biprodModule (ForgetEnrichment.to (Complex A) M) (ForgetEnrichment.to (Complex A) N))
    (fun _ => biprod.inr)
    (fun _ _ => (biprodHomMap_inr _ _).symm)

@[simp] lemma moduleBiprodFst_eval (M N : ModuleCategory A D) (x : D) :
    (moduleEvaluation A D x).map (moduleBiprodFst A D M N) = biprod.fst :=
  moduleMorphismMk_eval A D _ _ x
@[simp] lemma moduleBiprodSnd_eval (M N : ModuleCategory A D) (x : D) :
    (moduleEvaluation A D x).map (moduleBiprodSnd A D M N) = biprod.snd :=
  moduleMorphismMk_eval A D _ _ x
@[simp] lemma moduleBiprodInl_eval (M N : ModuleCategory A D) (x : D) :
    (moduleEvaluation A D x).map (moduleBiprodInl A D M N) = biprod.inl :=
  moduleMorphismMk_eval A D _ _ x
@[simp] lemma moduleBiprodInr_eval (M N : ModuleCategory A D) (x : D) :
    (moduleEvaluation A D x).map (moduleBiprodInr A D M N) = biprod.inr :=
  moduleMorphismMk_eval A D _ _ x

/-- objectwise 直和の射影と包含をまとめた Mathlib の bicone。 -/
def moduleBinaryBicone (M N : ModuleCategory A D) : BinaryBicone M N where
  pt := moduleBiprod A D M N
  fst := moduleBiprodFst A D M N
  snd := moduleBiprodSnd A D M N
  inl := moduleBiprodInl A D M N
  inr := moduleBiprodInr A D M N
  inl_fst := by
    apply moduleMorphism_ext
    intro x
    simp only [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id,
      moduleBiprodFst_eval, moduleBiprodInl_eval]
    exact biprod.inl_fst (X := (moduleEvaluation A D x).obj M)
      (Y := (moduleEvaluation A D x).obj N)
  inl_snd := by
    apply moduleMorphism_ext
    intro x
    simp only [CategoryTheory.Functor.map_comp, Functor.map_zero,
      moduleBiprodSnd_eval, moduleBiprodInl_eval]
    exact biprod.inl_snd (X := (moduleEvaluation A D x).obj M)
      (Y := (moduleEvaluation A D x).obj N)
  inr_fst := by
    apply moduleMorphism_ext
    intro x
    simp only [CategoryTheory.Functor.map_comp, Functor.map_zero,
      moduleBiprodFst_eval, moduleBiprodInr_eval]
    exact biprod.inr_fst (X := (moduleEvaluation A D x).obj M)
      (Y := (moduleEvaluation A D x).obj N)
  inr_snd := by
    apply moduleMorphism_ext
    intro x
    simp only [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id,
      moduleBiprodSnd_eval, moduleBiprodInr_eval]
    exact biprod.inr_snd (X := (moduleEvaluation A D x).obj M)
      (Y := (moduleEvaluation A D x).obj N)

/-- bicone の恒等分解は objectwise 直和の恒等分解。 -/
lemma moduleBinaryBicone_total (M N : ModuleCategory A D) :
    (moduleBinaryBicone A D M N).fst ≫ (moduleBinaryBicone A D M N).inl +
      (moduleBinaryBicone A D M N).snd ≫ (moduleBinaryBicone A D M N).inr =
        𝟙 (moduleBinaryBicone A D M N).pt := by
  apply moduleMorphism_ext
  intro x
  change (moduleEvaluation A D x).map
    (moduleBiprodFst A D M N ≫ moduleBiprodInl A D M N +
      moduleBiprodSnd A D M N ≫ moduleBiprodInr A D M N) =
        (moduleEvaluation A D x).map (𝟙 (moduleBiprod A D M N))
  simp only [Functor.map_add, CategoryTheory.Functor.map_comp,
    CategoryTheory.Functor.map_id, moduleBiprodFst_eval, moduleBiprodSnd_eval,
    moduleBiprodInl_eval, moduleBiprodInr_eval]
  exact biprod.total (X := (moduleEvaluation A D x).obj M)
    (Y := (moduleEvaluation A D x).obj N)

/-- objectwise 直和は積・余積の両方の普遍性を満たす。 -/
def moduleBinaryBiconeIsBilimit (M N : ModuleCategory A D) :
    (moduleBinaryBicone A D M N).IsBilimit :=
  isBinaryBilimitOfTotal _ (moduleBinaryBicone_total A D M N)

instance moduleHasBinaryBiproducts : HasBinaryBiproducts (ModuleCategory A D) where
  has_binary_biproduct M N :=
    hasBinaryBiproduct_of_total _ (moduleBinaryBicone_total A D M N)

/-- 零対象と二項直和から有限直和を供給する。一般の構成は Mathlib を再利用。 -/
instance moduleHasFiniteBiproducts : HasFiniteBiproducts (ModuleCategory A D) := by
  let : HasFiniteProducts (ModuleCategory A D) :=
    hasFiniteProducts_of_has_binary_and_terminal
  exact HasFiniteBiproducts.of_hasFiniteProducts

/-- 具体的 objectwise 直和と選ばれた圏の直和の標準同型。 -/
def moduleBiprodIso (M N : ModuleCategory A D) : moduleBiprod A D M N ≅ M ⊞ N :=
  biprod.uniqueUpToIso M N (moduleBinaryBiconeIsBilimit A D M N)

/-- 評価の加法性から Mathlib の二項直和保存を導く。 -/
instance moduleEvaluationPreservesBinaryBiproducts (x : D) :
    PreservesBinaryBiproducts (moduleEvaluation A D x) :=
  preservesBinaryBiproducts_of_preservesBiproducts _

/-- 評価は選ばれた圏の直和を既存複体の直和へ移す。 -/
def moduleEvaluationBiprodIso (M N : ModuleCategory A D) (x : D) :
    (moduleEvaluation A D x).obj (M ⊞ N) ≅
      (moduleEvaluation A D x).obj M ⊞ (moduleEvaluation A D x).obj N :=
  (moduleEvaluation A D x).mapBiprod M N

/-- 評価による比較同型は第一射影と可換。 -/
@[reassoc]
lemma moduleEvaluationBiprodIso_fst (M N : ModuleCategory A D) (x : D) :
    (moduleEvaluationBiprodIso A D M N x).hom ≫ biprod.fst =
      (moduleEvaluation A D x).map (biprod.fst : M ⊞ N ⟶ M) := by
  rw [moduleEvaluationBiprodIso, Functor.mapBiprod_hom]
  exact biprod.lift_fst _ _

/-- 評価による比較同型は第二射影と可換。 -/
@[reassoc]
lemma moduleEvaluationBiprodIso_snd (M N : ModuleCategory A D) (x : D) :
    (moduleEvaluationBiprodIso A D M N x).hom ≫ biprod.snd =
      (moduleEvaluation A D x).map (biprod.snd : M ⊞ N ⟶ N) := by
  rw [moduleEvaluationBiprodIso, Functor.mapBiprod_hom]
  exact biprod.lift_snd _ _
end SerrePositivity.DifferentialGraded
end

end Biproduct

/-! ## HomFunctor（旧 SerrePositivity/DifferentialGraded/Module/HomFunctor.lean） -/

/-! # 主 dg 加群 Hom end の通常射に対する関手性の成分公式 -/

@[expose] public section HomFunctor
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 加群射の成分を再び閉射にすると元の end 成分に戻る。 -/
lemma moduleEvaluation_closedMap (x : D) {M N : ModuleCategory A D} (f : M ⟶ N) :
    closedMap A (P := (ForgetEnrichment.to (Complex A) M).obj (op x))
      (Q := (ForgetEnrichment.to (Complex A) N).obj (op x)) ((moduleEvaluation A D x).map f) =
    ForgetEnrichment.homTo (Complex A) (C := RightModule A D) (X := M) (Y := N) f ≫
      moduleHomπ A D (ForgetEnrichment.to (Complex A) M) (ForgetEnrichment.to (Complex A) N) x :=
  closedMap_mapFromUnit A _ _ _

/-- end の後合成を評価すると通常の Hom 複体の後合成になる。 -/
@[reassoc]
lemma moduleHomWhiskerLeft_π {M N P : ModuleCategory A D} (f : N ⟶ P) (x : D) :
    eHomWhiskerLeft (Complex A) M f ≫
      moduleHomπ A D (ForgetEnrichment.to (Complex A) M) (ForgetEnrichment.to (Complex A) P) x =
    moduleHomπ A D (ForgetEnrichment.to (Complex A) M) (ForgetEnrichment.to (Complex A) N) x ≫
      homPostcompose ((moduleEvaluation A D x).obj M) ((moduleEvaluation A D x).map f) := by
  change (ρ_ (moduleHom A D (ForgetEnrichment.to (Complex A) M)
      (ForgetEnrichment.to (Complex A) N))).inv ≫
      moduleHom A D (ForgetEnrichment.to (Complex A) M) (ForgetEnrichment.to (Complex A) N) ◁
        ForgetEnrichment.homTo (Complex A) (C := RightModule A D) (X := N) (Y := P) f ≫
      moduleComposition A D (ForgetEnrichment.to (Complex A) M)
        (ForgetEnrichment.to (Complex A) N) (ForgetEnrichment.to (Complex A) P) ≫
      moduleHomπ A D (ForgetEnrichment.to (Complex A) M) (ForgetEnrichment.to (Complex A) P) x = _
  rw [moduleComposition_π, whiskerLeft_comp_tensorHom_assoc,
    rightUnitor_inv_comp_tensorHom_assoc, ← moduleEvaluation_closedMap,
    ← homPostcompose_closedMap]
  rfl

/-- end の前合成を評価すると通常の Hom 複体の前合成になる。 -/
@[reassoc]
lemma moduleHomWhiskerRight_π {M N P : ModuleCategory A D} (f : M ⟶ N) (x : D) :
    eHomWhiskerRight (Complex A) f P ≫
      moduleHomπ A D (ForgetEnrichment.to (Complex A) M) (ForgetEnrichment.to (Complex A) P) x =
    moduleHomπ A D (ForgetEnrichment.to (Complex A) N) (ForgetEnrichment.to (Complex A) P) x ≫
      homPrecompose ((moduleEvaluation A D x).map f) ((moduleEvaluation A D x).obj P) := by
  change (λ_ (moduleHom A D (ForgetEnrichment.to (Complex A) N)
      (ForgetEnrichment.to (Complex A) P))).inv ≫
      ForgetEnrichment.homTo (Complex A) (C := RightModule A D) (X := M) (Y := N) f ▷
        moduleHom A D (ForgetEnrichment.to (Complex A) N) (ForgetEnrichment.to (Complex A) P) ≫
      moduleComposition A D (ForgetEnrichment.to (Complex A) M)
        (ForgetEnrichment.to (Complex A) N) (ForgetEnrichment.to (Complex A) P) ≫
      moduleHomπ A D (ForgetEnrichment.to (Complex A) M) (ForgetEnrichment.to (Complex A) P) x = _
  rw [moduleComposition_π, whiskerRight_comp_tensorHom_assoc,
    leftUnitor_inv_comp_tensorHom_assoc, ← moduleEvaluation_closedMap,
    ← homPrecompose_closedMap]
  rfl
/-- 加群射の通常成分の零 cochain は end 成分の閉 cycle。 -/
lemma moduleEvaluation_cochain (x : D) {M N : ModuleCategory A D} (f : M ⟶ N) :
    Cochain.ofHom ((moduleEvaluation A D x).map f) =
    (moduleHomπ A D (ForgetEnrichment.to (Complex A) M) (ForgetEnrichment.to (Complex A) N) x).f 0
      (cycleFromUnit _
        (ForgetEnrichment.homTo (Complex A) (C := RightModule A D) (X := M) (Y := N) f)).val := by
  have h := mapFromUnit_cochain A ((ForgetEnrichment.to (Complex A) M).obj (op x))
    ((ForgetEnrichment.to (Complex A) N).obj (op x))
    (ForgetEnrichment.homTo (Complex A) (C := RightModule A D) (X := M) (Y := N) f ≫
      moduleHomπ A D (ForgetEnrichment.to (Complex A) M) (ForgetEnrichment.to (Complex A) N) x)
  rw [cycleFromUnit_postcomp] at h
  exact h
end SerrePositivity.DifferentialGraded
end

end HomFunctor

/-! ## HomWhisker（旧 SerrePositivity/DifferentialGraded/Module/HomWhisker.lean） -/

/-! # 元の加群型の全Homに値を持つ通常射の前後合成 -/

@[expose] public section HomWhisker
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Opposite
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 加群射の評価を元の複体型の間の射として固定する。 -/
def moduleMorphismComponent (M N : RightModule A D)
    (f : ForgetEnrichment.of (Complex A) M ⟶ ForgetEnrichment.of (Complex A) N) (x : D) :
    M.obj (op x) ⟶ N.obj (op x) :=
  (moduleEvaluation A D x).map f

/-- MathlibのHom後合成を元の加群型の主Hom間の射として公開する。 -/
def moduleHomPostcompose (M N P : RightModule A D)
    (f : ForgetEnrichment.of (Complex A) N ⟶ ForgetEnrichment.of (Complex A) P) :
    moduleHom A D M N ⟶ moduleHom A D M P :=
  eHomWhiskerLeft (Complex A) (ForgetEnrichment.of (Complex A) M) f

/-- MathlibのHom前合成を元の加群型の主Hom間の射として公開する。 -/
def moduleHomPrecompose (M N P : RightModule A D)
    (f : ForgetEnrichment.of (Complex A) M ⟶ ForgetEnrichment.of (Complex A) N) :
    moduleHom A D N P ⟶ moduleHom A D M P :=
  eHomWhiskerRight (Complex A) f (ForgetEnrichment.of (Complex A) P)

@[reassoc]
lemma moduleHomPostcompose_π (M N P : RightModule A D)
    (f : ForgetEnrichment.of (Complex A) N ⟶ ForgetEnrichment.of (Complex A) P) (x : D) :
    moduleHomPostcompose A D M N P f ≫ moduleHomπ A D M P x =
    moduleHomπ A D M N x ≫ homPostcompose (M.obj (op x))
      (moduleMorphismComponent A D N P f x) :=
  moduleHomWhiskerLeft_π A D f x

@[reassoc]
lemma moduleHomPrecompose_π (M N P : RightModule A D)
    (f : ForgetEnrichment.of (Complex A) M ⟶ ForgetEnrichment.of (Complex A) N) (x : D) :
    moduleHomPrecompose A D M N P f ≫ moduleHomπ A D M P x =
    moduleHomπ A D N P x ≫ homPrecompose (moduleMorphismComponent A D M N f x) (P.obj (op x)) :=
  moduleHomWhiskerRight_π A D f x

end SerrePositivity.DifferentialGraded
end

end HomWhisker

/-! ## HomIsoSquare（旧 SerrePositivity/DifferentialGraded/Module/HomIsoSquare.lean） -/

/-! # 可逆な加群射による全Hom可換四角形の逆向き -/

@[expose] public section HomIsoSquare
universe u v

noncomputable section
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]

lemma moduleHom_iso_square_inv {K : Complex A} {X Y X' Y' : ModuleCategory A B}
    (f : K ⟶ (X ⟶[Complex A] Y)) (g : K ⟶ (X' ⟶[Complex A] Y'))
    (a : X ≅ X') (b : Y ≅ Y')
    (h : f ≫ eHomWhiskerLeft (Complex A) X b.hom =
      g ≫ eHomWhiskerRight (Complex A) a.hom Y') :
    g ≫ eHomWhiskerLeft (Complex A) X' b.inv =
      f ≫ eHomWhiskerRight (Complex A) a.inv Y := by
  have hh := congrArg (fun k : K ⟶ (X ⟶[Complex A] Y') =>
    k ≫ eHomWhiskerLeft (Complex A) X b.inv ≫
      eHomWhiskerRight (Complex A) a.inv Y) h
  simp only [Category.assoc, ← eHomWhiskerLeft_comp_assoc, Iso.hom_inv_id,
    eHomWhiskerLeft_id, Category.id_comp] at hh
  rw [← eHom_whisker_exchange_assoc] at hh
  simp only [← eHomWhiskerRight_comp, Iso.inv_hom_id, eHomWhiskerRight_id,
    Category.comp_id] at hh
  exact hh.symm

lemma moduleIso_closed_hom_inv {X Y : ModuleCategory A B} (a : X ≅ Y) :
    (λ_ (𝟙_ (Complex A))).inv ≫
      (eHomEquiv (Complex A) a.hom ⊗ₘ eHomEquiv (Complex A) a.inv) ≫
        eComp (Complex A) X Y X = eId (Complex A) X := by
  rw [← eHomEquiv_comp, Iso.hom_inv_id, eHomEquiv_id]

end SerrePositivity.DifferentialGraded
end

end HomIsoSquare

/-! ## HomSquareComposition（旧 SerrePositivity/DifferentialGraded/Module/HomSquareComposition.lean） -/

/-! # 全Hom可換四角形の恒等と合成 -/

@[expose] public section HomSquareComposition
universe u v

noncomputable section
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]

lemma moduleHom_square_id {K : Complex A} {X Y : ModuleCategory A B}
    (f : K ⟶ (X ⟶[Complex A] Y)) :
    f ≫ eHomWhiskerLeft (Complex A) X (𝟙 Y) =
      f ≫ eHomWhiskerRight (Complex A) (𝟙 X) Y := by simp

lemma moduleHom_square_comp {K : Complex A} {X₁ Y₁ X₂ Y₂ X₃ Y₃ : ModuleCategory A B}
    (f : K ⟶ (X₁ ⟶[Complex A] Y₁)) (g : K ⟶ (X₂ ⟶[Complex A] Y₂))
    (h : K ⟶ (X₃ ⟶[Complex A] Y₃))
    (a : X₁ ⟶ X₂) (b : Y₁ ⟶ Y₂) (a' : X₂ ⟶ X₃) (b' : Y₂ ⟶ Y₃)
    (wf : f ≫ eHomWhiskerLeft (Complex A) X₁ b =
      g ≫ eHomWhiskerRight (Complex A) a Y₂)
    (wg : g ≫ eHomWhiskerLeft (Complex A) X₂ b' =
      h ≫ eHomWhiskerRight (Complex A) a' Y₃) :
    f ≫ eHomWhiskerLeft (Complex A) X₁ (b ≫ b') =
      h ≫ eHomWhiskerRight (Complex A) (a ≫ a') Y₃ := by
  calc
    _ = (f ≫ eHomWhiskerLeft (Complex A) X₁ b) ≫
        eHomWhiskerLeft (Complex A) X₁ b' := by
      rw [eHomWhiskerLeft_comp, Category.assoc]
    _ = (g ≫ eHomWhiskerRight (Complex A) a Y₂) ≫
        eHomWhiskerLeft (Complex A) X₁ b' := by rw [wf]
    _ = (g ≫ eHomWhiskerLeft (Complex A) X₂ b') ≫
        eHomWhiskerRight (Complex A) a Y₃ := by
      rw [Category.assoc, Category.assoc, eHom_whisker_exchange]
    _ = (h ≫ eHomWhiskerRight (Complex A) a' Y₃) ≫
        eHomWhiskerRight (Complex A) a Y₃ := by rw [wg]
    _ = _ := by rw [eHomWhiskerRight_comp, Category.assoc]

end SerrePositivity.DifferentialGraded
end

end HomSquareComposition

/-! ## HomElementComposition（旧 SerrePositivity/DifferentialGraded/Module/HomElementComposition.lean） -/

/-! # 主Hom endの斉次合成と通常射による制限の成分 -/

@[expose] public section HomElementComposition
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma moduleHomForward_π {M N P : RightModule A D} {p q n : ℤ}
    (z : (moduleHom A D M N).X p) (w : (moduleHom A D N P).X q)
    (hn : p + q = n) (x : D) :
    (moduleHomπ A D M P x).f n (forward A (x := M) (y := N) (z := P) z w hn) =
      (p * q).negOnePow • (((moduleHomπ A D M N x).f p z).comp
        ((moduleHomπ A D N P x).f q w) hn) := by
  have h := congrArg (fun a => a.f n
    (ιTensorObj (moduleHom A D M N) (moduleHom A D N P) p q n hn (z ⊗ₜ[A] w)))
    (moduleComposition_π A D M N P x)
  change (moduleHomπ A D M P x).f n (forward A (x := M) (y := N) (z := P) z w hn) =
    (enrichedComposition _ _ _).f n
      ((moduleHomπ A D M N x ⊗ₘ moduleHomπ A D N P x).f n
        (ιTensorObj (moduleHom A D M N) (moduleHom A D N P) p q n hn (z ⊗ₜ[A] w))) at h
  rw [tensorMap_apply, enrichedComposition_apply] at h
  exact h

lemma moduleHomWhiskerRight_apply_π {M N P : ModuleCategory A D} (f : M ⟶ N)
    (q : ℤ) (z : (moduleHom A D (ForgetEnrichment.to (Complex A) N)
      (ForgetEnrichment.to (Complex A) P)).X q) (x : D) :
    (moduleHomπ A D (ForgetEnrichment.to (Complex A) M)
      (ForgetEnrichment.to (Complex A) P) x).f q
        ((eHomWhiskerRight (Complex A) f P).f q z) =
      (Cochain.ofHom ((moduleEvaluation A D x).map f)).comp
        ((moduleHomπ A D (ForgetEnrichment.to (Complex A) N)
          (ForgetEnrichment.to (Complex A) P) x).f q z) (zero_add q) := by
  have h := congrArg (fun a => a.f q z) (moduleHomWhiskerRight_π A D (P := P) f x)
  exact h

end SerrePositivity.DifferentialGraded
end

end HomElementComposition
