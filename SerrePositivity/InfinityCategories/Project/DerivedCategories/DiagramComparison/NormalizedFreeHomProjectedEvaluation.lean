module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StandardDoldKanProjectedEvaluation
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.FreeChainsAdjunction

/-!
# 自由正規化鎖の指定随伴と実標準 Hom の成分

概要：指定自由鎖随伴の逆像を元の射影生成元で評価する。
方針：自由加群随伴の生成元則と Moore 射影の自然性・余単位を使う。
規約：元の随伴と生成元を保持する。IS-W2 B02の同じ証明の分割。
使われ方：HA 1.2.4、Kerodon 2.5（Tag 00ND）の実AWと自由鎖AWの成分照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
open CategoryTheory AlgebraicTopology DifferentialGraded
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories
open DifferentialGradedCategories
open scoped Simplicial
variable {R : Type u} [CommRing R]

/-- 概要：自由加群とMoore正規化の既存随伴の合成。
方針：同じ二つの随伴を固定する。規約：係数環R。
使われ方：HA 1.2.4 の自由生成元での逆随伴の評価。 -/
def freeMooreChainsAdjunction :
    ((Functor.whiskeringRight SimplexCategoryᵒᵖ (Type u) (ModuleCat R)).obj
      (ModuleCat.free R) ⋙ normalizedMooreComplex (ModuleCat R)) ⊣
    ((Abelian.DoldKan.Γ : ChainComplex (ModuleCat R) ℕ ⥤ SimplicialObject (ModuleCat R)) ⋙
      (Functor.whiskeringRight SimplexCategoryᵒᵖ (ModuleCat R) (Type u)).obj
        (forget (ModuleCat R))) :=
  (Adjunction.whiskerRight SimplexCategoryᵒᵖ (ModuleCat.adj R)).comp
    (Abelian.DoldKan.equivalence : SimplicialObject (ModuleCat R) ≌
      ChainComplex (ModuleCat R) ℕ).toAdjunction

/-- 概要：自由正規化鎖の逆随伴を射影生成元で計算する。
方針：同じMoore射影の自然性と自由随伴の生成元則。
規約：任意の単体集合と次数。使われ方：HA 1.2.4 の同じ自由鎖射の評価。 -/
theorem normalizedFreeHomEquiv_symm_projected_eval (S : SSet.{u})
    (K : ChainComplex (ModuleCat R) ℕ)
    (f : S ⟶ (Abelian.DoldKan.Γ.obj K) ⋙ forget (ModuleCat R)) (n : ℕ)
    (s : S.obj (Opposite.op ⦋n⦌)) :
    (((freeMooreChainsAdjunction (R := R)).homEquiv S K).symm f).f n
      ((DoldKan.PInftyToNormalizedMooreComplex (S ⋙ ModuleCat.free R)).f n
        (ModuleCat.freeMk s)) =
    ((DoldKan.PInftyToNormalizedMooreComplex (Abelian.DoldKan.Γ.obj K)).f n ≫
      (Abelian.DoldKan.equivalence.counitIso.hom.app K).f n) (f.app _ s) := by
  dsimp only
  let a := Adjunction.whiskerRight SimplexCategoryᵒᵖ (ModuleCat.adj R)
  let b := (Abelian.DoldKan.equivalence : SimplicialObject (ModuleCat R) ≌
    ChainComplex (ModuleCat R) ℕ).toAdjunction
  let g := (a.homEquiv S (Abelian.DoldKan.Γ.obj K)).symm f
  have hn := congrArg (fun t => t.f n)
    (DoldKan.PInftyToNormalizedMooreComplex_naturality g)
  have h := ConcreteCategory.congr_hom hn (ModuleCat.freeMk s)
  have hg : g.app (Opposite.op ⦋n⦌) (ModuleCat.freeMk s) = f.app _ s := by
    have h' := ConcreteCategory.congr_hom
      (NatTrans.congr_app ((a.homEquiv S _).apply_symm_apply f) (Opposite.op ⦋n⦌)) s
    exact h'
  change (DoldKan.PInftyToNormalizedMooreComplex (Abelian.DoldKan.Γ.obj K)).f n
      (g.app (Opposite.op ⦋n⦌) (ModuleCat.freeMk s)) =
    ((normalizedMooreComplex (ModuleCat R)).map g).f n
      ((DoldKan.PInftyToNormalizedMooreComplex (S ⋙ ModuleCat.free R)).f n
        (ModuleCat.freeMk s)) at h
  rw [hg] at h
  simp only [freeMooreChainsAdjunction, Adjunction.comp_homEquiv, Equiv.symm_trans_apply]
  change ((b.homEquiv _ K).symm g).f n _ = _
  rw [Adjunction.homEquiv_symm_apply]
  change (Abelian.DoldKan.equivalence.counitIso.hom.app K).f n
    (((normalizedMooreComplex (ModuleCat R)).map g).f n _) = _
  exact congrArg ((Abelian.DoldKan.equivalence.counitIso.hom.app K).f n) h.symm

variable {D : Type v} [DGCategory R D]

/-- 概要：指定標準DK同型の忘却後の射を固定する。
方針：同じ同型を忘却関手へ送る。規約：標準Homから実Γ Homへ。
使われ方：HA 1.2.4 の自由鎖逆随伴の型の固定。 -/
def standardDoldKanSpaceMap (x y : D) :
    standardHomSpace (R := R) x y ⟶
      (Abelian.DoldKan.Γ.obj (connectiveHomComplex (R := R) x y)) ⋙
        forget (ModuleCat R) :=
  Functor.whiskerRight (standardDoldKanModuleIso (R := R) x y).hom
    (forget (ModuleCat R))

/-- 概要：実標準Homへの射の逆随伴の成分は元の最上位成分。
方針：同じ自由逆随伴の公式に指定DK評価を代入する。
規約：全正次数の指定生成元。使われ方：HA 1.2.4 の実豊穣合成との接続。 -/
theorem normalizedFreeStandardHom_positive_eval (S : SSet.{u}) (x y : D)
    (f : S ⟶ standardHomSpace (R := R) x y) (n : ℕ)
    (s : S.obj (Opposite.op ⦋n + 1⦌)) :
    let g : (normalizedMooreComplex (ModuleCat R)).obj (S ⋙ ModuleCat.free R) ⟶
        connectiveHomComplex (R := R) x y :=
      ((freeMooreChainsAdjunction (R := R)).homEquiv S
        (connectiveHomComplex (R := R) x y)).symm (f ≫ standardDoldKanSpaceMap x y)
    (connectiveHomComplex_positiveIso (R := R) x y n).hom
      (g.f (n + 1)
        ((DoldKan.PInftyToNormalizedMooreComplex (S ⋙ ModuleCat.free R)).f (n + 1)
          (ModuleCat.freeMk s))) =
    standardTopEval (R := R) x y (n + 1) (f.app _ s) := by
  let t : S ⟶ (Abelian.DoldKan.Γ.obj (connectiveHomComplex (R := R) x y)) ⋙
      forget (ModuleCat R) := f ≫ standardDoldKanSpaceMap x y
  have h := normalizedFreeHomEquiv_symm_projected_eval S
    (connectiveHomComplex (R := R) x y) t (n + 1) s
  have hp := congrArg (connectiveHomComplex_positiveIso (R := R) x y n).hom h
  have he := ConcreteCategory.congr_hom
    (standardDoldKanModuleIso_positive_projected_eval (R := R) x y n) (f.app _ s)
  simp only [ModuleCat.comp_apply] at he
  dsimp only [t, standardDoldKanSpaceMap, NatTrans.comp_app,
    Functor.whiskerRight_app] at hp
  simp only [ModuleCat.comp_apply] at hp
  exact hp.trans he

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
