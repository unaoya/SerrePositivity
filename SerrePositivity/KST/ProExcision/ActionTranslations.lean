module

public import SerrePositivity.KST.ProExcision.SimplicialAction

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
# 群状モノイドの作用による各頂点の可逆性

概要：群状単体モノイドの各頂点は、作用先のホモトピー不変な像で可逆に作用する。
方針：作用の頂点への制限と辺に沿うホモトピーを作り、π₀ の逆元を使う。
規約：モノイドの各単体に逆元を要求しない。
使われ方：KST Lemma A.2 の ψ のファイバー上の同値性。
-/

universe u v w
namespace SerrePositivity.KST.ProExcision
open CategoryTheory Opposite MonoidalCategory CartesianMonoidalCategory
open SerrePositivity.KST.Comparison
open scoped Simplicial
variable {G H : SimplicialObject MonCat.{u}}

/-- 概要：単体的作用を台単体集合の積からの写像として表す。
方針：各次数の作用を、全ての単体射への自然性でつなぐ。
規約：作用先の群性はまだ不要。使われ方：KST Lemma A.2 の頂点と辺による作用。 -/
def simplicialActionMap (A : SimplicialMonoidAction G H) :
    monoidSpace G ⊗ monoidSpace H ⟶ monoidSpace H where
  app n := TypeCat.ofHom (fun p ↦ A.action n p.1 p.2)
  naturality n m f := by
    apply ConcreteCategory.hom_ext
    intro p
    exact (A.naturality f p.1 p.2).symm

/-- 概要：作用するモノイドの頂点による作用先の単体写像。
方針：頂点の定数写像と作用先の恒等写像を作用へ合成する。
規約：台単体集合の射。使われ方：KST Lemma A.2 の各ファイバーの写像。 -/
def actionTranslation (A : SimplicialMonoidAction G H) (a : G.obj (op ⦋0⦌)) :
    monoidSpace H ⟶ monoidSpace H :=
  lift (SSet.const a) (𝟙 (monoidSpace H)) ≫ simplicialActionMap A

/-- 概要：単位頂点の作用は恒等写像。
方針：定数単体の単位保存と次数ごとの作用の単位則を使う。
規約：各次数の厳密な等式。使われ方：KST Lemma A.2 の逆作用の検証。 -/
theorem actionTranslation_one (A : SimplicialMonoidAction G H) :
    actionTranslation A 1 = 𝟙 (monoidSpace H) := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro x
  change A.action n ((G.map (SimplexCategory.const n.unop ⦋0⦌ 0).op).hom 1) x = x
  rw [map_one, map_one]
  rfl

/-- 概要：頂点の作用の合成は積頂点の作用。
方針：定数単体と自己準同型への作用が積を保つことを使う。
規約：先に a、後に b は b*a。使われ方：KST Lemma A.2 の π₀ の逆成分の利用。 -/
theorem actionTranslation_comp (A : SimplicialMonoidAction G H)
    (a b : G.obj (op ⦋0⦌)) :
    actionTranslation A a ≫ actionTranslation A b = actionTranslation A (b * a) := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro x
  change A.action n ((G.map (SimplexCategory.const n.unop ⦋0⦌ 0).op).hom b)
      (A.action n ((G.map (SimplexCategory.const n.unop ⦋0⦌ 0).op).hom a) x) =
    A.action n ((G.map (SimplexCategory.const n.unop ⦋0⦌ 0).op).hom (b * a)) x
  rw [map_mul, map_mul]
  rfl

/-- 概要：辺で結ばれた頂点による二つの作用の間の単体的ホモトピー。
方針：区間を辺へ送り、作用先と組にして作用写像へ合成する。
規約：辺の逆向きの存在は不要。使われ方：KST Lemma A.2 の成分に依存する作用。 -/
def actionTranslationHomotopy (A : SimplicialMonoidAction G H)
    {a b : G.obj (op ⦋0⦌)} (e : (monoidSpace G).Edge a b) :
    SSet.Homotopy (actionTranslation A a) (actionTranslation A b) where
  h := lift (snd _ _ ≫ SSet.yonedaEquiv.symm e.edge) (fst _ _) ≫ simplicialActionMap A
  h₀ := by
    dsimp only [actionTranslation]
    rw [← Category.assoc, comp_lift]
    simp only [SSet.ι₀_snd_assoc, SSet.ι₀_fst, SSet.const_comp]
    congr 2
    apply congrArg (SSet.const (X := monoidSpace H))
    rw [SSet.yonedaEquiv_symm_app]
    have hδ : SSet.stdSimplex.objEquiv (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
        SimplexCategory.δ (1 : Fin 2) := by
      ext i
      fin_cases i
      rfl
    rw [hδ]
    exact e.src_eq
  h₁ := by
    dsimp only [actionTranslation]
    rw [← Category.assoc, comp_lift]
    simp only [SSet.ι₁_snd_assoc, SSet.ι₁_fst, SSet.const_comp]
    congr 2
    apply congrArg (SSet.const (X := monoidSpace H))
    rw [SSet.yonedaEquiv_symm_app]
    have hδ : SSet.stdSimplex.objEquiv (SSet.stdSimplex.obj₀Equiv.symm (1 : Fin 2)) =
        SimplexCategory.δ (0 : Fin 2) := by
      ext i
      fin_cases i
      rfl
    rw [hδ]
    exact e.tgt_eq
  rel := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.property

/-- 概要：ホモトピー不変な関手の下での作用は頂点の連結成分に依存する。
方針：辺に沿う作用の実ホモトピーで π₀ の商へ降ろす。
規約：関手のホモトピー不変性は所有レーンの入力。
使われ方：KST Lemma A.2 の群状性からの可逆性。 -/
def actionTranslationClass (A : SimplicialMonoidAction G H)
    {D : Type w} [Category.{v} D] (L : SSet.{u} ⥤ D)
    (hL : ∀ {f g : monoidSpace H ⟶ monoidSpace H}, SSet.Homotopy f g → L.map f = L.map g) :
    SSet.π₀ (monoidSpace G) → (L.obj (monoidSpace H) ⟶ L.obj (monoidSpace H)) :=
  SSet.π₀.lift (fun (a : G.obj (op ⦋0⦌)) ↦ L.map (actionTranslation A a))
    (fun {_ _} e ↦ hL (actionTranslationHomotopy A e))

/-- 概要：同じ成分の頂点の作用はホモトピー不変な関手の下で等しい。
方針：連結成分へ降ろした作用へ等式を適用する。
規約：作用先の群性は不要。使われ方：KST Lemma A.2 の逆成分の代表元の利用。 -/
theorem actionTranslation_map_eq (A : SimplicialMonoidAction G H)
    {D : Type w} [Category.{v} D] (L : SSet.{u} ⥤ D)
    (hL : ∀ {f g : monoidSpace H ⟶ monoidSpace H}, SSet.Homotopy f g → L.map f = L.map g)
    {a b : G.obj (op ⦋0⦌)}
    (hab : SSet.π₀.mk (X := monoidSpace G) a = SSet.π₀.mk (X := monoidSpace G) b) :
    L.map (actionTranslation A a) = L.map (actionTranslation A b) :=
  congrArg (actionTranslationClass A L hL) hab

/-- 概要：群状モノイドの各頂点はホモトピー不変な像で可逆に作用する。
方針：π₀ の逆成分の代表を選び、積成分の単位への一致から左右の逆射を作る。
規約：群状性は K-L2 の π₀ の群条件。各次数の G の逆元は選ばない。
使われ方：KST Lemma A.2 の ψ のファイバー上の可逆性。 -/
def grouplikeActionIso (A : SimplicialMonoidAction G H)
    (hG : SimplicialMonoid.IsGrouplike G) {D : Type w} [Category.{v} D]
    (L : SSet.{u} ⥤ D)
    (hL : ∀ {f g : monoidSpace H ⟶ monoidSpace H}, SSet.Homotopy f g → L.map f = L.map g)
    (a : G.obj (op ⦋0⦌)) : L.obj (monoidSpace H) ≅ L.obj (monoidSpace H) := by
  letI := SimplicialMonoid.componentsMonoid G
  let u := (hG (SSet.π₀.mk (X := monoidSpace G) a)).unit
  have hu : (u : SSet.π₀ (monoidSpace G)) = SSet.π₀.mk (X := monoidSpace G) a := (hG _).unit_spec
  let b : G.obj (op ⦋0⦌) := Classical.choose (SSet.π₀.mk_surjective (u⁻¹).val)
  have hb := Classical.choose_spec (SSet.π₀.mk_surjective (u⁻¹).val)
  have hab : SSet.π₀.mk (X := monoidSpace G) (a * b) = SSet.π₀.mk (1 : G.obj (op ⦋0⦌)) := by
    change SSet.π₀.mk (X := monoidSpace G) a * SSet.π₀.mk (X := monoidSpace G) b = 1
    rw [hb, ← hu]
    exact Units.mul_inv u
  have hba : SSet.π₀.mk (X := monoidSpace G) (b * a) = SSet.π₀.mk (1 : G.obj (op ⦋0⦌)) := by
    change SSet.π₀.mk (X := monoidSpace G) b * SSet.π₀.mk (X := monoidSpace G) a = 1
    rw [hb, ← hu]
    exact Units.inv_mul u
  exact
    { hom := L.map (actionTranslation A a)
      inv := L.map (actionTranslation A b)
      hom_inv_id := by
        rw [← L.map_comp, actionTranslation_comp, actionTranslation_map_eq A L hL hba,
          actionTranslation_one, L.map_id]
      inv_hom_id := by
        rw [← L.map_comp, actionTranslation_comp, actionTranslation_map_eq A L hL hab,
          actionTranslation_one, L.map_id] }

end SerrePositivity.KST.ProExcision
