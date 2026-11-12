module

public import SerrePositivity.KST.Spectra.Limits.SpectrumPullbackMonomorphisms
public import SerrePositivity.KST.Spectra.CofibrantOmegaSequence
public import SerrePositivity.KST.Spectra.PostMappingFibration

/-!
概要：引き戻し列の随伴構造射と loop による引き戻し保存の厳密な比較。
方針：右随伴による標準同型を作り、その二つの射影で随伴構造射を計算する。
規約：ここでは π_* 同型の保存と Ω 条件をまだ主張しない。
使われ方：BF 1978 §2、HA §1.4.2、HTT 4.2.4.1 の Sp の引き戻し対象。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open SerrePositivity.KST.Spectra
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section

local instance : (PointedObject.basedHomFunctor PointedSimplicialSet.circle.{u}).IsRightAdjoint :=
  (PointedSimplicialSet.smashHomAdjunction PointedSimplicialSet.circle.{u}).isRightAdjoint

/-- 概要：引き戻しの loop と二つの loop 射の引き戻しの標準同型。
方針：円からの点つき内部 Hom の右随伴性による引き戻し保存を使う。
規約：Kan 性や fibration 性を要求しない通常の厳密な同型。
使われ方：Sp の引き戻し列の随伴構造射の比較。 -/
def loopPullbackIso {E X B : PointedSimplicialSet.{u}} (f : E ⟶ B) (g : X ⟶ B) :
    _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace (pullback f g) ≅
      pullback (PointedObject.basedHomMap PointedSimplicialSet.circle.{u} f)
        (PointedObject.basedHomMap PointedSimplicialSet.circle.{u} g) :=
  PreservesPullback.iso (PointedObject.basedHomFunctor PointedSimplicialSet.circle.{u}) f g

/-- 概要：loop と引き戻しの標準同型は第一射影と可換。
方針：右随伴による引き戻し比較の第一射影の計算を使う。
規約：点つき単体的集合の射の厳密な等式。
使われ方：引き戻しの随伴構造射を第一成分で計算する。 -/
lemma loopPullbackIso_hom_fst {E X B : PointedSimplicialSet.{u}} (f : E ⟶ B) (g : X ⟶ B) :
    (loopPullbackIso f g).hom ≫ pullback.fst _ _ =
      PointedObject.basedHomMap PointedSimplicialSet.circle.{u} (pullback.fst f g) :=
  PreservesPullback.iso_hom_fst (PointedObject.basedHomFunctor PointedSimplicialSet.circle.{u})
    f g

/-- 概要：loop と引き戻しの標準同型は第二射影と可換。
方針：右随伴による引き戻し比較の第二射影の計算を使う。
規約：点つき単体的集合の射の厳密な等式。
使われ方：引き戻しの随伴構造射を第二成分で計算する。 -/
lemma loopPullbackIso_hom_snd {E X B : PointedSimplicialSet.{u}} (f : E ⟶ B) (g : X ⟶ B) :
    (loopPullbackIso f g).hom ≫ pullback.snd _ _ =
      PointedObject.basedHomMap PointedSimplicialSet.circle.{u} (pullback.snd f g) :=
  PreservesPullback.iso_hom_snd (PointedObject.basedHomFunctor PointedSimplicialSet.circle.{u})
    f g

/-- 概要：元の随伴構造射が引き戻しの間に誘導する比較射。
方針：各射影と元の随伴構造射を合成し、列の射の随伴可換式で貼る。
規約：通常の引き戻しの射で、Kan 性や fibration 性は不要。
使われ方：引き戻しの Ω 条件で検証すべき実際の比較射を指定する。 -/
def pullbackAdjointMap {E X B : KanSequence.{u}}
    (f : KanSequence.Hom E B) (g : KanSequence.Hom X B) (n : ℕ) :
    pullback (f.app n) (g.app n) ⟶
      pullback (PointedObject.basedHomMap PointedSimplicialSet.circle.{u} (f.app (n + 1)))
        (PointedObject.basedHomMap PointedSimplicialSet.circle.{u} (g.app (n + 1))) :=
  pullback.lift
    (pullback.fst (f.app n) (g.app n) ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspensionLoopEquiv _ _ (E.sigma n))
    (pullback.snd (f.app n) (g.app n) ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspensionLoopEquiv _ _ (X.sigma n)) (by
      rw [Category.assoc, ← f.adjoint_comm n, ← Category.assoc, pullback.condition,
        Category.assoc, g.adjoint_comm n, ← Category.assoc])

/-- 概要：引き戻し列の構造射の随伴は標準同型の下で元の随伴の引き戻し比較射となる。
方針：二つの射影で検査し、随伴の Hom 同値の両変数の自然性を使う。
規約：全ての列の厳密な等式であり、Ω 条件は仮定しない。
使われ方：BF 1978 §2、Sp の引き戻しの Ω 条件を比較射の π_* 同型へ帰着する。 -/
lemma pullbackSigma_adjoint {E X B : KanSequence.{u}}
    (f : KanSequence.Hom E B) (g : KanSequence.Hom X B) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspensionLoopEquiv _ _ (KanSequence.pullbackSigma f g n) ≫
        (loopPullbackIso (f.app (n + 1)) (g.app (n + 1))).hom =
      pullbackAdjointMap f g n := by
  apply pullback.hom_ext
  · rw [Category.assoc, loopPullbackIso_hom_fst, pullbackAdjointMap, pullback.lift_fst]
    let adj := PointedSimplicialSet.smashHomAdjunction PointedSimplicialSet.circle.{u}
    change adj.homEquiv _ _ (KanSequence.pullbackSigma f g n) ≫
        (PointedObject.basedHomFunctor PointedSimplicialSet.circle.{u}).map
          (pullback.fst (f.app (n + 1)) (g.app (n + 1))) =
      pullback.fst (f.app n) (g.app n) ≫ adj.homEquiv _ _ (E.sigma n)
    rw [← adj.homEquiv_naturality_right, KanSequence.pullbackSigma, pullback.lift_fst]
    exact adj.homEquiv_naturality_left (pullback.fst (f.app n) (g.app n)) (E.sigma n)
  · rw [Category.assoc, loopPullbackIso_hom_snd, pullbackAdjointMap, pullback.lift_snd]
    let adj := PointedSimplicialSet.smashHomAdjunction PointedSimplicialSet.circle.{u}
    change adj.homEquiv _ _ (KanSequence.pullbackSigma f g n) ≫
        (PointedObject.basedHomFunctor PointedSimplicialSet.circle.{u}).map
          (pullback.snd (f.app (n + 1)) (g.app (n + 1))) =
      pullback.snd (f.app n) (g.app n) ≫ adj.homEquiv _ _ (X.sigma n)
    rw [← adj.homEquiv_naturality_right, KanSequence.pullbackSigma, pullback.lift_snd]
    exact adj.homEquiv_naturality_left (pullback.snd (f.app n) (g.app n)) (X.sigma n)

/-- 概要：一脚が段ごとに fibration の引き戻し列の Ω 条件は実際の比較射で検出できる。
方針：随伴構造射の計算式と loop と引き戻しの同型の π_* 同型を使う。
規約：比較射の π_* 同型性そのものはこの補題では仮定側として残す。
使われ方：Sp の引き戻しの Ω 条件で残る比較定理の正確な界面。 -/
lemma pullbackSequence_omega_iff {E X B : KanSequence.{u}}
    (f : KanSequence.Hom E B) (g : KanSequence.Hom X B)
    [∀ n, Fibration (f.app n).right] :
    (KanSequence.pullbackSequence f g).OmegaCondition ↔
      ∀ n, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (pullbackAdjointMap f g n).right := by
  have hi (n : ℕ) : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism
      (loopPullbackIso (f.app (n + 1)) (g.app (n + 1))).hom.right :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanPiIsomorphism.of_iso
      (X := (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace (pullback (f.app (n + 1)) (g.app (n + 1)))).right)
      (Y := (pullback
        (PointedObject.basedHomMap PointedSimplicialSet.circle.{u} (f.app (n + 1)))
        (PointedObject.basedHomMap PointedSimplicialSet.circle.{u} (g.app (n + 1)))).right)
      (PointedSimplicialSet.forget.mapIso (loopPullbackIso _ _))
  constructor
  · intro h n
    have he := (h n).comp (hi n)
    have hc := congrArg Under.Hom.right (pullbackSigma_adjoint f g n)
    simp only [Under.comp_right] at hc
    change _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism
      ((_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspensionLoopEquiv _ _ (KanSequence.pullbackSigma f g n)).right ≫ _) at he
    rw [hc] at he
    exact he
  · intro h n
    have hc := congrArg Under.Hom.right (pullbackSigma_adjoint f g n)
    simp only [Under.comp_right] at hc
    have he := h n
    rw [← hc] at he
    exact he.of_comp (hi n)

end
end SerrePositivity.InfinityCategories.HomotopyLimits
