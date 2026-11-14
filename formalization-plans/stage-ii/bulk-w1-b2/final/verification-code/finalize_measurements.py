from pathlib import Path
import json,datetime,collections,hashlib,re,os
w=Path('/tmp/bulk-w1-b2');complete=json.load(open(w/'preservation-complete.json'));assert complete['modules']==9518
keys=json.load(open(w/'key-measurements.json'));start=None
for line in (w/'preservation-slot-004.log').read_text().splitlines():
 try:d=json.loads(line)
 except ValueError:continue
 if isinstance(d,dict) and 'slot_started' in d:start=datetime.datetime.fromisoformat(d['slot_started']);break
assert start is not None
end=datetime.datetime.fromtimestamp(complete['finished'],datetime.timezone(datetime.timedelta(hours=9)));holds=[]
for row in keys['rows']:
 a=datetime.datetime.fromisoformat(row['started'])
 if a>=start and 'preserve_slot.py' in row['command']:holds.append(row)
build=json.load(open(w/'preview-build-complete.json'));receipts=[]
for p in (w/'preview-build').glob('group-*.json'):
 r=json.load(open(p))
 if r['rc']==0 and r['global_source_signature']==build['global_source_signature']:receipts.append(r)
assert sum(len(r['modules']) for r in receipts)==9550
newday=[r for r in keys['rows'] if (a:=datetime.datetime.fromisoformat(r['started']).astimezone(datetime.timezone(datetime.timedelta(hours=9)))) .date()==datetime.date(2026,11,13) and 8<=a.hour<23]
summary={'fixed_math_base':'0e8c854208151bc054e15ba3ba183a931b630b1c','target_build_final_successful_groups':len(receipts),'target_build_final_successful_group_seconds':sum(r['seconds'] for r in receipts),'target_build_modules':9550,'full_preservation_started':start.isoformat(),'full_preservation_finished':end.isoformat(),'full_preservation_wall_seconds_including_day_queue':(end-start).total_seconds(),'full_preservation_completed_lease_seconds':sum(r['hold_seconds'] for r in holds),'full_preservation_queue_seconds':sum(r['wait_seconds'] for r in holds),'full_preservation_leases':len(holds),'day_new_rule_completed_leases':len(newday),'day_new_rule_maximum_hold_seconds':max((r['hold_seconds'] for r in newday),default=0),'warning':'Final build group totals are process wall seconds, not a fresh clean build. Full-preservation wall includes the actual daytime queue and guard retries; capture scheduling changed from sequential to memory-guarded pairs. B3 root/all audits/verify are not measured here.'}
sleep=json.load(open(w/'sleep-intervals.json'))
intervals=[(datetime.datetime.fromisoformat(x['started']),datetime.datetime.fromisoformat(x['finished'])) for x in sleep['intervals']]
def suspension(a,b):return sum(max(0,(min(b,y)-max(a,x)).total_seconds()) for x,y in intervals)
summary['observed_sleep_seconds_in_full_preservation']=suspension(start,end)
summary['full_preservation_wall_excluding_observed_sleep_seconds']=(end-start).total_seconds()-suspension(start,end)
summary['full_preservation_hold_excluding_observed_sleep_seconds']=sum(r['hold_seconds']-suspension(datetime.datetime.fromisoformat(r['started']),datetime.datetime.fromisoformat(r['finished'])) for r in holds)
summary['maximum_raw_day_lease_seconds']=summary['day_new_rule_maximum_hold_seconds']
summary['day_lease_maximum_excluding_observed_sleep_seconds']=max((r['hold_seconds']-suspension(datetime.datetime.fromisoformat(r['started']),datetime.datetime.fromisoformat(r['finished'])) for r in newday),default=0)
summary['suspension_note']='OS sleep pauses the ordinary monotonic process timers. Raw wall-clock holds and OS-sleep-adjusted holds are both retained, without calling long suspended wall-clock holds 280 seconds.'
(w/'final-time-measurements.json').write_text(json.dumps(summary,ensure_ascii=False,indent=2));print(summary)
