module

public import SerrePositivity.KST.Comparison.FiberwiseAnodyne

/-!
# 部分単体集合上の指定を保つホモトピーの持ち上げ

概要：Kan fibration に対し、区間端点と部分対象上で指定した写像を同時に延長する。
方針：単射と区間端点の pushout-product に右持ち上げ性を適用する。
規約：Segal 1974 Proposition 1.6 の対角模型の補助。モデル構造の公理は仮定しない。
使われ方：horn の逆像を保つ収縮の持ち上げ。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial
open SerrePositivity.SimplicialModel

/--
概要：除く頂点の番号で指定する区間端点。
方針：点との積の同型と標準単体の余面を合成する。
規約：番号 1 は始点、番号 0 は終点を表す。
使われ方：両向きのホモトピーの持ち上げを同じ命題で扱う。
-/
def intervalEndpoint (X : SSet.{u}) (i : Fin 2) : X ⟶ X ⊗ (Δ[1] : SSet.{u}) :=
  (AnodyneHomotopy.pointTensorIso X).hom ≫ X ◁ SSet.stdSimplex.δ i

/--
概要：点との積の標準同型の自然性。
方針：全次数で第一成分を送る式を評価する。
規約：区間端点を合成したときの整合。
使われ方：端点での条件を pushout-product の条件に移す。
-/
theorem pointTensorIso_naturality {A X : SSet.{u}} (i : A ⟶ X) :
    (AnodyneHomotopy.pointTensorIso A).hom ≫ i ▷ (Δ[0] : SSet.{u}) =
      i ≫ (AnodyneHomotopy.pointTensorIso X).hom := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro x
  rfl

/--
概要：区間端点の包含は anodyne である。
方針：点との積の同型と anodyne な余面の合成を使う。
規約：番号 1 は始点、0 は終点。
使われ方：Kan fibration に沿うホモトピーの持ち上げ。
-/
theorem intervalEndpoint_anodyne (X : SSet.{u}) (ε : Fin 2) :
    SSet.anodyneExtensions (intervalEndpoint X ε) :=
  SSet.anodyneExtensions.comp_mem _ _ (SSet.anodyneExtensions.of_isIso _)
    ((AnodyneHomotopy.delta_anodyne ε (if ε = 0 then 1 else 0)
      (by fin_cases ε <;> decide)).whiskerLeft X)

/--
概要：指定した区間端点から Kan fibration に沿って持ち上げる。
方針：端点の anodyne 性と horn の右持ち上げ性を使う。
規約：Segal 1974 Proposition 1.6 の補助。始点・終点の両方を扱う。
使われ方：horn を保つ基底の収縮を全空間に持ち上げる。
-/
theorem interval_lift {X E B : SSet.{u}} (p : E ⟶ B)
    (hp : SSet.modelCategoryQuillen.J.rlp p) (ε : Fin 2) (a : X ⟶ E)
    (b : X ⊗ (Δ[1] : SSet.{u}) ⟶ B) (ha : a ≫ p = intervalEndpoint X ε ≫ b) :
    ∃ h : X ⊗ (Δ[1] : SSet.{u}) ⟶ E, intervalEndpoint X ε ≫ h = a ∧ h ≫ p = b := by
  have : HasLiftingProperty (intervalEndpoint X ε) p := intervalEndpoint_anodyne X ε _ hp
  let sq : CommSq a (intervalEndpoint X ε) p b := ⟨ha⟩
  exact ⟨sq.lift, sq.fac_left, sq.fac_right⟩

/--
概要：部分対象と区間端点で指定された写像を Kan fibration に沿って延長する。
方針：単射と anodyne な端点の pushout-product から持ち上げを得る。
規約：Segal 1974 Proposition 1.6 の補助。端点は番号 1 が始点、0 が終点。
使われ方：逆像の部分単体集合を保つホモトピーを全空間へ延長する。
-/
theorem relative_interval_lift {A X E B : SSet.{u}} (i : A ⟶ X) [Mono i]
    (p : E ⟶ B) (hp : SSet.modelCategoryQuillen.J.rlp p) (ε : Fin 2)
    (a : X ⟶ E) (v : A ⊗ (Δ[1] : SSet.{u}) ⟶ E)
    (b : X ⊗ (Δ[1] : SSet.{u}) ⟶ B)
    (ha : i ≫ a = intervalEndpoint A ε ≫ v)
    (hap : a ≫ p = intervalEndpoint X ε ≫ b)
    (hvp : v ≫ p = i ▷ (Δ[1] : SSet.{u}) ≫ b) :
    ∃ h : X ⊗ (Δ[1] : SSet.{u}) ⟶ E,
      intervalEndpoint X ε ≫ h = a ∧ i ▷ (Δ[1] : SSet.{u}) ≫ h = v ∧ h ≫ p = b := by
  let e := SSet.stdSimplex.δ.{u} ε
  have he : SSet.anodyneExtensions e :=
    AnodyneHomotopy.delta_anodyne ε (if ε = 0 then 1 else 0) (by fin_cases ε <;> decide)
  let pp := Functor.PushoutObjObj.ofHasPushout (curriedTensor SSet.{u}) i e
  have hpp : SSet.anodyneExtensions pp.ι := SSet.anodyneExtensions_pushoutObjObjι pp he
  have : HasLiftingProperty pp.ι p := hpp _ hp
  let a' := fst X (Δ[0] : SSet.{u}) ≫ a
  have hc : i ▷ (Δ[0] : SSet.{u}) ≫ a' = A ◁ e ≫ v := by
    apply (cancel_epi (AnodyneHomotopy.pointTensorIso A).hom).mp
    rw [← Category.assoc, pointTensorIso_naturality]
    dsimp only [a']
    rw [Category.assoc, ← Category.assoc (AnodyneHomotopy.pointTensorIso X).hom,
      pointTensorIso_fst, Category.id_comp]
    exact ha
  let c := pp.isPushout.desc a' v hc
  have hap' : a' ≫ p = X ◁ e ≫ b := by
    apply (cancel_epi (AnodyneHomotopy.pointTensorIso X).hom).mp
    dsimp only [a']
    rw [← Category.assoc, ← Category.assoc, pointTensorIso_fst, Category.id_comp]
    exact hap
  have hcp : c ≫ p = pp.ι ≫ b := by
    apply pp.isPushout.hom_ext
    · rw [← Category.assoc, pp.isPushout.inl_desc, ← Category.assoc, pp.inl_ι]
      exact hap'
    · rw [← Category.assoc, pp.isPushout.inr_desc, ← Category.assoc, pp.inr_ι]
      exact hvp
  let sq : CommSq c pp.ι p b := ⟨hcp⟩
  have hstart : X ◁ e ≫ sq.lift = a' := by
    rw [show X ◁ e = pp.inl ≫ pp.ι from pp.inl_ι.symm, Category.assoc, sq.fac_left]
    exact pp.isPushout.inl_desc _ _ _
  have hrel : i ▷ (Δ[1] : SSet.{u}) ≫ sq.lift = v := by
    rw [show i ▷ (Δ[1] : SSet.{u}) = pp.inr ≫ pp.ι from pp.inr_ι.symm,
      Category.assoc, sq.fac_left]
    exact pp.isPushout.inr_desc _ _ _
  refine ⟨sq.lift, ?_, hrel, sq.fac_right⟩
  dsimp only [intervalEndpoint]
  rw [Category.assoc, hstart]
  dsimp only [a']
  rw [← Category.assoc, pointTensorIso_fst, Category.id_comp]

end SerrePositivity.KST.Comparison
