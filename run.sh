#1/bin/sh
export W1=$(curl -s -H "Content-Type: application/json" -X POST -d '{"caID": "PiggyBank2Contract", "caWallet":{"getWallet": 1}}' http://localhost:9080/api/contract/activate | jq .unContractInstanceId | tr -d '"')
export W2=$(curl -s -H "Content-Type: application/json" -X POST -d '{"caID": "PiggyBank2Contract", "caWallet":{"getWallet": 2}}' http://localhost:9080/api/contract/activate | jq .unContractInstanceId | tr -d '"')
export W3=$(curl -s -H "Content-Type: application/json" -X POST -d '{"caID": "PiggyBank2Contract", "caWallet":{"getWallet": 3}}' http://localhost:9080/api/contract/activate | jq .unContractInstanceId | tr -d '"')
export W4=$(curl -s -H "Content-Type: application/json" -X POST -d '{"caID": "PiggyBank2Contract", "caWallet":{"getWallet": 4}}' http://localhost:9080/api/contract/activate | jq .unContractInstanceId | tr -d '"')
export W5=$(curl -s -H "Content-Type: application/json" -X POST -d '{"caID": "PiggyBank2Contract", "caWallet":{"getWallet": 5}}' http://localhost:9080/api/contract/activate | jq .unContractInstanceId | tr -d '"')

sleep 4
curl -H "Content-Type: application/json" -X POST -d 299999 http://localhost:9080/api/contract/instance/$W1/endpoint/put &&
sleep 4
curl -H "Content-Type: application/json" -X POST -d 299999 http://localhost:9080/api/contract/instance/$W2/endpoint/put &&
sleep 4
curl -H "Content-Type: application/json" -X POST -d 299999 http://localhost:9080/api/contract/instance/$W2/endpoint/put &&
sleep 4
curl -H "Content-Type: application/json" -X POST -d "true" http://localhost:9080/api/contract/instance/$W3/endpoint/empty
sleep 4
curl -H "Content-Type: application/json" -X POST -d "false" http://localhost:9080/api/contract/instance/$W3/endpoint/empty
sleep 4
curl -H "Content-Type: application/json" -X POST -d "true" http://localhost:9080/api/contract/instance/$W4/endpoint/empty
sleep 4
curl -H "Content-Type: application/json" -X POST -d 900000 http://localhost:9080/api/contract/instance/$W3/endpoint/put
sleep 4
curl -H "Content-Type: application/json" -X POST -d "true" http://localhost:9080/api/contract/instance/$W5/endpoint/empty
