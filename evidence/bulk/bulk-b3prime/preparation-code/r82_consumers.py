from pathlib import Path
import json
R=Path('/tmp/bulk-b3prime-preview');paths=['BhattScholze/Perfectoidization/Derived/RootAdjunction','BhattScholze/IntegralPerfectoidization/Completion/IntegralClosureCompletion','BhattScholze/IntegralPerfectoidization/Approximation/IntegralApproximation','BhattScholze/IntegralPerfectoidization/Approximation/PerfectoidFilteredColimit','BhattScholze/Perfectoidization/Arc/Descent/ArcPerfectoidBase'];rows=[]
old='public import SerrePositivity.BhattScholze.Perfectoidization.Derived.Interface';new='public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.RingInterface'
for x in paths:
 p=R/'SerrePositivity'/(x+'.lean');s=p.read_text();assert s.count(old)==1;p.write_text(s.replace(old,new));rows.append({'path':p.relative_to(R).as_posix(),'old_import':old,'new_import':new})
Path('/tmp/bulk-b3prime/r82-consumers.json').write_text(json.dumps(rows,indent=2));print('consumer import replacements',len(rows))
